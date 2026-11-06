/*-
 * SPDX-License-Identifier: LicenseRef-scancode-bsd-unchanged
 *
 * Copyright (c) 2020-2026 Baptiste Daroussin <bapt@FreeBSD.org>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer
 *    in this position and unchanged.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR(S) ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR(S) BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <sys/param.h>
#include <sys/wait.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>

#include <ctype.h>
#include <fcntl.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <fetch.h>
#include <paths.h>
#include <poll.h>
#include <unistd.h>

#include <bsd_compat.h>

#include "pkg.h"
#include "private/event.h"
#include "private/pkg.h"
#include "private/fetch.h"
#include <utlist.h>
#include "private/utils.h"

struct http_mirror {
	struct url *url;
	bool reldoc;
	struct http_mirror *next;
};

#define PKG_HTTP_MIRROR_LIST_MAX_SIZE	(1024 * 1024)
#define PKG_HTTP_MIRROR_LIST_MAX_LINE	MAXPATHLEN
#define PKG_HTTP_MIRROR_LIST_MAX_ENTRIES	256

static void
gethttpmirrors(struct pkg_repo *repo, const char *url, bool withdoc) {
	FILE *f;
	char line[PKG_HTTP_MIRROR_LIST_MAX_LINE];
	char *walk;
	size_t linelen, total = 0, nmirrors = 0;
	int c;
	struct http_mirror *m, *new_mirrors = NULL, *tmp;
	struct url *u;
	bool accepted = false;

	/*
	 * The mirror list is advisory and is not protected by repository
	 * signatures.  Do not reuse its connection so an early error does not
	 * make fclose() drain an arbitrary response body.
	 */
	if ((f = fetchGetURL(url, "c")) == NULL)
		return;

	for (;;) {
		linelen = 0;
		while ((c = fgetc(f)) != EOF) {
			if (++total > PKG_HTTP_MIRROR_LIST_MAX_SIZE) {
				pkg_emit_error("HTTP mirror list exceeds %d bytes",
				    PKG_HTTP_MIRROR_LIST_MAX_SIZE);
				goto done;
			}
			if (c == '\0' || linelen == sizeof(line) - 1) {
				pkg_emit_error("HTTP mirror list contains an invalid line");
				goto done;
			}
			if (c == '\n')
				break;
			line[linelen++] = c;
		}
		if (ferror(f))
			goto done;
		if (linelen == 0 && c == EOF)
			break;
		line[linelen] = '\0';

		if (strncmp(line, "URL:", 4) == 0) {
			walk = line;
			if (linelen > 0 && walk[linelen - 1] == '\r')
				walk[linelen - 1] = '\0';

			walk += 4;
			while (isspace(*walk)) {
				walk++;
			}
			if (*walk == '\0')
				continue;

			if ((u = fetchParseURL(walk)) != NULL) {
				if (nmirrors == PKG_HTTP_MIRROR_LIST_MAX_ENTRIES) {
					fetchFreeURL(u);
					pkg_emit_error("HTTP mirror list has too many entries");
					goto done;
				}
				m = xmalloc(sizeof(struct http_mirror));
				m->reldoc = withdoc;
				m->url = u;
				m->next = NULL;
				LL_APPEND(new_mirrors, m);
				nmirrors++;
			}
		}
		if (c == EOF)
			break;
	}
	accepted = true;

done:
	fclose(f);
	if (accepted) {
		LL_CONCAT(repo->http, new_mirrors);
	} else {
		LL_FOREACH_SAFE(new_mirrors, m, tmp) {
			fetchFreeURL(m->url);
			free(m);
		}
	}
}

/*
 * Append one mirror to a repository's HTTP mirror list. Exposed so that
 * the failover logic in libfetch_open() can be exercised by unit tests
 * without having to run a real HTTP server to serve a mirrorlist.
 */
void
pkg_repo_http_mirror_append(struct pkg_repo *repo, const char *url,
    bool reldoc)
{
	struct http_mirror *m;
	struct url *u;

	u = fetchParseURL(url);
	if (u == NULL)
		return;
	m = xmalloc(sizeof(*m));
	m->url = u;
	m->reldoc = reldoc;
	m->next = NULL;
	LL_APPEND(repo->http, m);
}

/*
 * The server refused the request itself (authentication, a malformed or
 * unsupported request, a bad URL): asking it again later cannot help.
 * Anything else, including errors libfetch does not classify, may be
 * transient.
 */
static bool
libfetch_permanent(void)
{
	switch (fetchLastErrCode) {
	case FETCH_AUTH:
	case FETCH_PROTO:
	case FETCH_URL:
		return (true);
	default:
		return (false);
	}
}

static int
libfetch_open_retry(struct pkg_repo *repo, struct fetch_item *fi,
    int64_t max_retry, bool recovery)
{
	struct url *u;
	struct url *repourl;
	int64_t retry;
	int64_t fetch_timeout;
	char docpath[MAXPATHLEN];
	char zone[MAXHOSTNAMELEN + 24];
	char *doc, *reldoc, *opts;
	struct dns_srvinfo *srv_current = NULL;
	struct http_mirror *http_current = NULL;
	struct url_stat st;
	time_t ims;
	int retcode;
	bool transient = false;
	sb_t fetchOpts = sb_init();

	if (max_retry < 0)
		max_retry = 0;
	fetch_timeout = pkg_object_int(pkg_config_get("FETCH_TIMEOUT"));

	fetchTimeout = (int)MIN(fetch_timeout, INT_MAX);
	if (fetch_timeout > 0) {
		fetchSpeedLimit = 2 * 1024;	/* 2KB/s, same as curl fetcher */
		fetchSpeedTime = (int)MIN(fetch_timeout, INT_MAX);
	}

	u = fetchParseURL(fi->url);
	if (u == NULL) {
		pkg_emit_error("%s: parse error", fi->url);
		return (EPKG_FATAL);
	}

	repourl = fetchParseURL(repo->url);
	if (repourl == NULL) {
		pkg_emit_error("%s: parse error", repo->url);
		fetchFreeURL(u);
		return (EPKG_FATAL);
	}
	retry = max_retry;
	doc = u->doc;
	reldoc = doc + strlen(repourl->doc);
	fetchFreeURL(repourl);

	ims = fi->mtime;
	u->ims_time = ims;
	if (recovery && fi->http_validator[0] != '\0')
		u->if_range = fi->http_validator;
	if (fi->offset > 0)
		u->offset = fi->offset;

	/* HTTP authentication */
	const char *userpasswd = get_http_auth();
	if (userpasswd != NULL) {
		const char *colon = strchr(userpasswd, ':');
		if (colon != NULL) {
			size_t ulen = colon - userpasswd;
			if (ulen < sizeof(u->user))
				strlcpy(u->user, userpasswd, ulen + 1);
			strlcpy(u->pwd, colon + 1, sizeof(u->pwd));
		}
	}

	pkg_dbg(PKG_DBG_FETCH, 1, "libfetch> connecting");

	/*
	 * Build the server list once, before entering the fetch loop. For
	 * SRV repositories this resolves the DNS SRV records (RFC 2782); for
	 * HTTP mirror repositories it fetches the mirror list. A plain
	 * repository has a single implicit server: the configured URL.
	 *
	 * Try every server once before waiting. Only a failed pass through
	 * the whole list consumes a retry round, so a dead mirror does not
	 * delay access to a healthy one. Backoff is shared by all mirrors:
	 * adding mirrors does not multiply the time spent sleeping. A pass
	 * in which every server refused the request itself is not retried.
	 */
	if (repo->mirror_type == SRV &&
	    strncmp(u->scheme, "http", 4) == 0) {
		if (repo->srv == NULL) {
			snprintf(zone, sizeof(zone),
			    "_%s._tcp.%s", u->scheme, u->host);
			repo->srv = dns_getsrvinfo(zone);
		}
		if (repo->srv == NULL) {
			pkg_emit_error("SRV lookup failed for '%s', "
			    "falling back to %s://%s", zone, u->scheme, u->host);
			if (u->port == 0)
				u->port = strcmp(u->scheme, "https") == 0 ?
				    443 : 80;
		} else {
			srv_current = repo->srv;
		}
	} else if (repo->mirror_type == HTTP &&
	    strncmp(u->scheme, "http", 4) == 0) {
		if (u->port == 0) {
			if (strcmp(u->scheme, "https") == 0)
				u->port = 443;
			else
				u->port = 80;
		}
		snprintf(zone, sizeof(zone),
		    "%s://%s:%d", u->scheme, u->host, u->port);
		if (repo->http == NULL)
			gethttpmirrors(repo, zone, false);
		if (repo->http == NULL)
			gethttpmirrors(repo, repo->url, true);
		if (repo->http == NULL) {
			pkg_emit_error("Could not retrieve mirror list from "
			    "'%s', falling back to %s://%s", zone,
			    u->scheme, u->host);
		} else {
			http_current = repo->http;
		}
	}

	while (repo->fh == NULL) {
		if (repo->mirror_type == SRV && srv_current != NULL) {
			strlcpy(u->host, srv_current->host, sizeof(u->host));
			u->port = srv_current->port;
		} else if (repo->mirror_type == HTTP &&
		    http_current != NULL) {
			strlcpy(u->scheme, http_current->url->scheme,
			    sizeof(u->scheme));
			strlcpy(u->host, http_current->url->host,
			    sizeof(u->host));
			snprintf(docpath, sizeof(docpath), "%s%s",
			    http_current->url->doc,
			    http_current->reldoc ? reldoc : doc);
			u->doc = docpath;
			u->port = http_current->url->port;
		}
		sb_cat(&fetchOpts, "i");
		/* Discard abandoned recovery bodies instead of draining them. */
		if (recovery)
			sb_cat(&fetchOpts, "c");
		if (repo->ip == IPV4)
			sb_cat(&fetchOpts, "4");
		else if (repo->ip == IPV6)
			sb_cat(&fetchOpts, "6");

		if (ctx.debug_level >= 4)
			sb_cat(&fetchOpts, "v");

		opts = sb_get(&fetchOpts);
		pkg_dbg(PKG_DBG_FETCH, 1,
		    "libfetch> fetching from: %s://%s%s%s%s with opts \"%s\"",
		    u->scheme,
		    u->user,
		    u->user[0] != '\0' ? "@" : "",
		    u->host,
		    u->doc,
		    opts);

		repo->fh = fetchXGet(u, &st, opts);
		free(opts);
		if (repo->fh == NULL) {
			if (fetchLastErrCode == FETCH_RESTART) {
				retcode = EPKG_AGAIN;
				goto out;
			}
			if (fetchLastErrCode == FETCH_OK) {
				retcode = EPKG_UPTODATE;
				goto out;
			}
			/* During recovery a connection reset is another failed open. */
			if (fetchLastErrCode == FETCH_ABORT && !recovery) {
				retcode = EPKG_CANCEL;
				goto out;
			}
			if (fetchLastErrCode == FETCH_UNAVAIL) {
				if (!repo->silent)
					pkg_emit_error("%s://%s%s%s%s: %s",
					    u->scheme,
					    u->user,
					    u->user[0] != '\0' ? "@" : "",
					    u->host,
					    u->doc,
					    fetchLastErrString);
				retcode = EPKG_ENOENT;
				goto out;
			}
			if (fetchLastErrCode == FETCH_NETWORK ||
			    fetchLastErrCode == FETCH_RESOLV ||
			    fetchLastErrCode == FETCH_DOWN) {
				pkg_emit_pkg_errno(EPKG_NONETWORK,
				    "libfetch_open", NULL);
			}
			if (!libfetch_permanent())
				transient = true;
			if (max_retry <= 0) {
				/* No retry budget at all, no failover. */
				break;
			}
			/* Try the next mirror without a backoff delay. */
			if (repo->mirror_type == SRV && srv_current != NULL) {
				srv_current = srv_current->next;
				if (srv_current != NULL)
					continue;
			} else if (repo->mirror_type == HTTP &&
			    http_current != NULL) {
				http_current = http_current->next;
				if (http_current != NULL)
					continue;
			}
			/*
			 * Waiting cannot cure a pass in which every server
			 * refused the request outright; give up at once.
			 */
			if (!transient || --retry <= 0)
				break;
			transient = false;
			fetch_retry_wait(max_retry - retry);
			/* Start another pass, including the plain-URL fallback. */
			if (repo->mirror_type == SRV)
				srv_current = repo->srv;
			else if (repo->mirror_type == HTTP)
				http_current = repo->http;
			continue;
		}

		/*
		 * Some servers answer 200 to a conditional request even
		 * when the file did not change.  The mtime of the response
		 * tells whether it must be downloaded again.
		 */
		if (fi->offset == 0 && ims != 0 && st.mtime != 0 &&
		    st.mtime <= ims) {
			pkg_dbg(PKG_DBG_FETCH, 1, "libfetch> %s: up to "
			    "date (mtime %ld)", u->doc, (long)ims);
			fh_close(repo);
			retcode = EPKG_UPTODATE;
			goto out;
		}
	}
	if (repo->fh == NULL) {
		if (!repo->silent)
			pkg_emit_error("%s://%s%s%s%s: %s",
			    u->scheme,
			    u->user,
			    u->user[0] != '\0' ? "@" : "",
			    u->host,
			    u->doc,
			    fetchLastErrString);
		retcode = EPKG_FATAL;
		goto out;
	}
	fi->size = st.size > 0 ? st.size : 0;
	fi->mtime = st.mtime;
	/* A server ignoring the range request starts over at 0. */
	fi->offset = u->offset;
	strlcpy(fi->http_validator, st.validator, sizeof(fi->http_validator));
	retcode = EPKG_OK;
out:
	/*
	 * While a mirror is in use, u->doc aliases the on-stack docpath
	 * buffer.  Hand libfetch back its own heap pointer before freeing:
	 * every exit must go through here, because returning early with
	 * the alias in place makes fetchFreeURL() free the stack (this was
	 * a real crash with mirror_type "http" from 2.0 until 2.8.2).
	 */
	u->doc = doc;
	fetchFreeURL(u);
	return (retcode);
}

int
libfetch_open(struct pkg_repo *repo, struct fetch_item *fi)
{
	/* No validator is stored with partial files from an earlier fetch. */
	fi->http_validator[0] = '\0';
	if (fi->offset > 0) {
		fi->offset = 0;
		fi->mtime = 0;
	}
	return (libfetch_open_retry(repo, fi,
	    pkg_object_int(pkg_config_get("FETCH_RETRY")), false));
}

/*
 * Make dest hold exactly the first offset bytes of the file, positioned at
 * their end.  It already does unless the server ignored a range request and
 * started over, in which case the bytes past offset are dropped.
 */
static int
libfetch_seek(int dest, off_t offset)
{
	struct stat st;

	if (fstat(dest, &st) == -1) {
		pkg_emit_errno("fstat", "fetch destination");
		return (EPKG_FATAL);
	}
	if (st.st_size < offset) {
		pkg_emit_error("cannot resume the transfer: the destination "
		    "holds %jd bytes, not %jd", (intmax_t)st.st_size,
		    (intmax_t)offset);
		return (EPKG_FATAL);
	}
	if (st.st_size > offset && ftruncate(dest, offset) == -1) {
		pkg_emit_errno("ftruncate", "fetch destination");
		return (EPKG_FATAL);
	}
	if (lseek(dest, offset, SEEK_SET) == -1) {
		pkg_emit_errno("lseek", "fetch destination");
		return (EPKG_FATAL);
	}
	return (EPKG_OK);
}

/*
 * Reconnect once through the mirrors. Only reuse bytes when an HTTP
 * validator identifies the original representation. EPKG_AGAIN requests
 * a full restart on the next budgeted attempt (e.g. after HTTP 416).
 */
static int
libfetch_reopen(struct pkg_repo *repo, struct fetch_item *fi, off_t *offset)
{
	off_t size = fi->size;
	time_t mtime = fi->mtime;
	int ret;

	fh_close(repo);
	/* A body cut short by EOF can leave a dead connection in the cache. */
	http_cache_flush();
	if (fi->http_validator[0] == '\0')
		*offset = 0;
	fi->offset = *offset;
	/* If-Modified-Since would allow a bodyless 304 during recovery. */
	fi->mtime = 0;
	ret = libfetch_open_retry(repo, fi, 1, true);
	if (ret != EPKG_OK || (fi->offset > 0 && fi->mtime == 0))
		fi->mtime = mtime;
	if (ret == EPKG_OK && fi->offset > 0 && size > 0 &&
	    fi->size != size) {
		fh_close(repo);
		ret = EPKG_AGAIN;
	}
	if (ret == EPKG_AGAIN) {
		*offset = 0;
		fi->http_validator[0] = '\0';
	}
	return (ret == EPKG_UPTODATE ? EPKG_FATAL : ret);
}

/*
 * Recover interrupted transfers to regular files. FETCH_RETRY bounds the
 * total reconnection passes, including full restarts and failed opens;
 * progress never replenishes this budget. Each pass has its own backoff
 * but no nested connection retries.
 */
int
libfetch_fetch(struct pkg_repo *repo, int dest, struct fetch_item *fi)
{
	struct stat st;
	int64_t max_retry, retry = 0;
	off_t reached = 0;
	int err = 0, ret;
	bool resuming = false;

	/* Resuming needs a destination that can be truncated and seeked. */
	if (fstat(dest, &st) == -1 || !S_ISREG(st.st_mode))
		return (stdio_fetch(repo, dest, fi));

	max_retry = pkg_object_int(pkg_config_get("FETCH_RETRY"));
	for (;;) {
		if (resuming) {
			if (retry >= max_retry) {
				fetch_emit_interrupted(fi, reached, err);
				return (EPKG_FATAL);
			}
			fetch_retry_wait(++retry);
			ret = libfetch_reopen(repo, fi, &reached);
			/* Classify failed reopens like the open loop does. */
			if (ret == EPKG_AGAIN ||
			    (ret == EPKG_FATAL && !libfetch_permanent()))
				continue;
			if (ret != EPKG_OK)
				return (ret);
		}

		if ((ret = libfetch_seek(dest, fi->offset)) != EPKG_OK)
			return (ret);
		ret = stdio_fetch_part(repo, dest, fi, resuming, &reached,
		    &err);
		if (ret != EPKG_AGAIN)
			return (ret);
		if (retry >= max_retry ||
		    (fi->size > 0 && reached >= fi->size) ||
		    (fi->expected_size > 0 && reached >= fi->expected_size)) {
			fetch_emit_interrupted(fi, reached, err);
			return (EPKG_FATAL);
		}
		pkg_emit_notice("%s: interrupted after %jd bytes (%s), "
		    "retrying (%jd/%jd)", fi->url, (intmax_t)reached,
		    err != 0 ? strerror(err) : "connection closed",
		    (intmax_t)(retry + 1), (intmax_t)max_retry);
		resuming = true;
	}
}

void
libfetch_cleanup(struct pkg_repo *repo)
{
	if (repo->mirror_type == HTTP) {
		struct http_mirror *m, *tmp;
		LL_FOREACH_SAFE(repo->http, m, tmp) {
			fetchFreeURL(m->url);
			free(m);
		}
		repo->http = NULL;
	} else if (repo->mirror_type == SRV) {
		struct dns_srvinfo *s, *stmp;
		LL_FOREACH_SAFE(repo->srv, s, stmp) {
			free(s);
		}
		repo->srv = NULL;
	}
	fh_close(repo);
	http_cache_flush();
}
