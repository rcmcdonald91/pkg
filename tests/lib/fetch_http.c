/*-
 * Copyright (c) 2026 Baptiste Daroussin <bapt@FreeBSD.org>
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <atf-c.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <pkg.h>
#include <private/pkg.h>
#include <private/fetch.h>
#include <private/event.h>

/*
 * These tests exercise the HTTP-mirror logic in libfetch_open() directly:
 *
 *  - a "dead" mirror is an http:// URL to 127.0.0.1:1, where nothing listens,
 *    so the connection is refused immediately (a retryable FETCH_DOWN);
 *  - an "alive" mirror is a small HTTP server forked on a random localhost
 *    port (see http_server_start()), answering 200, 404 or 304 as the test
 *    requires.
 *
 * The mirror list is pre-populated via pkg_repo_http_mirror_append(), so the
 * mirrorlist-discovery step is skipped; only the server-walking loop runs.
 *
 * While a mirror is in use u->doc points at a stack buffer, so every exit of
 * that loop has to hand libfetch back its own pointer before releasing the
 * URL. Each case below leaves libfetch_open() through a different exit.
 */

static void
make_repo_file(const char *dir, const char *name, const char *content)
{
	int fd;

	fd = openat(open(dir, O_DIRECTORY), name, O_CREAT | O_WRONLY, 0644);
	ATF_REQUIRE_MSG(fd != -1, "openat %s/%s: %s", dir, name,
	    strerror(errno));
	if (content != NULL)
		ATF_REQUIRE(write(fd, content, strlen(content)) != -1);
	close(fd);
}

static struct pkg_repo
make_http_repo(void)
{
	struct pkg_repo repo = {0};

	repo.mirror_type = HTTP;
	/* Only used to compute the relative document path; never fetched. */
	repo.url = "http://pkg.test/";
	return (repo);
}

/* Bind an ephemeral loopback port; the caller starts listening. */
static int
http_server_socket(int *port)
{
	struct sockaddr_in addr = {
		.sin_family = AF_INET,
		.sin_addr.s_addr = htonl(INADDR_LOOPBACK),
	};
	socklen_t len = sizeof(addr);
	int fd;

	fd = socket(AF_INET, SOCK_STREAM, 0);
	ATF_REQUIRE_MSG(fd != -1, "socket: %s", strerror(errno));
	ATF_REQUIRE_MSG(bind(fd, (struct sockaddr *)&addr, len) == 0,
	    "bind: %s", strerror(errno));
	ATF_REQUIRE(getsockname(fd, (struct sockaddr *)&addr, &len) == 0);
	*port = ntohs(addr.sin_port);
	return (fd);
}

/*
 * Observe real attempts and waits through the debug event interface. Check
 * each event before it happens, so an unexpected 60-second wait fails at
 * once rather than making a timing-sensitive assertion after the fetch.
 */
struct retry_trace {
	const char *expected;
	size_t pos;
};

static int
retry_event(void *data, struct pkg_event *ev)
{
	struct retry_trace *trace = data;
	const char *msg;
	char action;

	if (ev->type != PKG_EVENT_DEBUG)
		return (0);
	msg = ev->e_debug.msg;
	if (strstr(msg, "libfetch> fetching from:") != NULL)
		action = strstr(msg, "/a/") != NULL ? 'a' :
		    strstr(msg, "/b/") != NULL ? 'b' : 'f';
	else if (strstr(msg, "Fetch: waiting") != NULL)
		action = 'w';
	else
		return (0);
	ATF_REQUIRE_EQ_MSG(trace->expected[trace->pos], action,
	    "unexpected retry event %zu: %s (expected %s)",
	    trace->pos, msg, trace->expected);
	trace->pos++;
	return (0);
}

static void
retry_trace_start(struct retry_trace *trace)
{
	ctx.debug_level = 1;
	ctx.debug_flags = PKG_DBG_FETCH;
	pkg_event_register(retry_event, trace);
}

static void
retry_trace_stop(struct retry_trace *trace)
{
	pkg_event_register(NULL, NULL);
	ATF_REQUIRE_EQ(strlen(trace->expected), trace->pos);
}

enum http_reply {
	HTTP_REPLY_OK,
	HTTP_REPLY_NOT_FOUND,
	HTTP_REPLY_NOT_MODIFIED,
};

struct http_server {
	pid_t	pid;
	int	port;
};

/*
 * Child side of the test server: handle one request, answer according to
 * reply, then exit. last_modified, when not NULL, is sent as the
 * Last-Modified header of a 200 reply.
 */
static void
http_server_serve(int listen_fd, const char *dir, enum http_reply reply,
    const char *last_modified)
{
	struct sockaddr_in caddr;
	socklen_t clen = sizeof(caddr);
	char req[4096], path[MAXPATHLEN], fbuf[4096], hdr[512];
	size_t rlen = 0;
	ssize_t flen;
	char *p, *e;
	int cfd, ffd;

	signal(SIGPIPE, SIG_IGN);

	cfd = accept(listen_fd, (struct sockaddr *)&caddr, &clen);
	if (cfd < 0)
		_exit(1);

	/*
	 * Read the full request before replying. libfetch writes the
	 * request line by line (GET, Host, Accept, ...), each with a
	 * separate write(); if we reply after a single read we may
	 * close the socket while libfetch is still writing the
	 * remaining headers, which makes it die of SIGPIPE. Keep
	 * reading until we have the end-of-headers marker.
	 */
	for (;;) {
		ssize_t n = read(cfd, req + rlen, sizeof(req) - 1 - rlen);

		if (n <= 0)
			_exit(1);
		rlen += (size_t)n;
		req[rlen] = '\0';
		if (strstr(req, "\r\n\r\n") != NULL)
			break;
		if (rlen >= sizeof(req) - 1)
			break;
	}

	if (reply == HTTP_REPLY_NOT_MODIFIED) {
		snprintf(hdr, sizeof(hdr),
		    "HTTP/1.1 304 Not Modified\r\n"
		    "Connection: close\r\n\r\n");
		write(cfd, hdr, strlen(hdr));
		close(cfd);
		_exit(0);
	}

	if (reply == HTTP_REPLY_OK) {
		/* Parse "GET /path HTTP/1.x" */
		p = strchr(req, ' ');
		if (p == NULL)
			_exit(1);
		p++;
		e = strchr(p, ' ');
		if (e == NULL)
			_exit(1);
		*e = '\0';

		snprintf(path, sizeof(path), "%s%s", dir, p);
		ffd = open(path, O_RDONLY);
		if (ffd >= 0) {
			flen = read(ffd, fbuf, sizeof(fbuf));
			if (flen < 0)
				flen = 0;
			close(ffd);
			if (last_modified != NULL)
				snprintf(hdr, sizeof(hdr),
				    "HTTP/1.1 200 OK\r\n"
				    "Content-Length: %zd\r\n"
				    "Last-Modified: %s\r\n"
				    "Connection: close\r\n\r\n",
				    flen, last_modified);
			else
				snprintf(hdr, sizeof(hdr),
				    "HTTP/1.1 200 OK\r\n"
				    "Content-Length: %zd\r\n"
				    "Connection: close\r\n\r\n", flen);
			write(cfd, hdr, strlen(hdr));
			write(cfd, fbuf, flen);
			close(cfd);
			_exit(0);
		}
	}

	snprintf(hdr, sizeof(hdr),
	    "HTTP/1.1 404 Not Found\r\n"
	    "Content-Length: 0\r\n"
	    "Connection: close\r\n\r\n");
	write(cfd, hdr, strlen(hdr));
	close(cfd);
	_exit(0);
}

/*
 * Fork a test server on a random localhost port for a single request.
 */
static struct http_server
http_server_start(const char *dir, enum http_reply reply,
    const char *last_modified)
{
	struct http_server srv;
	int listen_fd;

	listen_fd = http_server_socket(&srv.port);
	ATF_REQUIRE(listen(listen_fd, 1) == 0);

	srv.pid = fork();
	ATF_REQUIRE_MSG(srv.pid != -1, "fork: %s", strerror(errno));

	if (srv.pid == 0) {
		alarm(30);
		http_server_serve(listen_fd, dir, reply, last_modified);
		_exit(1);
	}
	close(listen_fd);

	return (srv);
}

static void
http_server_stop(struct http_server *srv)
{
	waitpid(srv->pid, NULL, 0);
}

/*
 * A scripted server for the transfer resume tests: it answers one request
 * per step, in order, each time with the rest of the file from the offset
 * of the request's range (the whole file when there is none), and exits 0
 * once every step was served.  It exits with 50 + step when a request does
 * not ask for the expected range, and with 100 + step on a request reaching
 * a STEP_UNEXPECTED step, so the test can tell exactly which requests pkg
 * made.
 */
enum http_step_kind {
	/* Announce the rest of the file, send len bytes of it, close. */
	STEP_DROP,
	/* Same, but reset the connection instead of closing it. */
	STEP_RESET,
	/* Send the rest of the file. */
	STEP_SERVE,
	/* Answer 200 with the whole file, ignoring the range. */
	STEP_IGNORE_RANGE,
	/* Fail to reopen the transfer with a retryable HTTP error. */
	STEP_RETRY,
	/* Fail with 429, which libfetch does not classify. */
	STEP_RATE_LIMIT,
	/* Return 503 for len seconds from the first request, then serve. */
	STEP_OUTAGE,
	/* pkg must not make this request. */
	STEP_UNEXPECTED,
	STEP_BAD_RANGE,
	STEP_STALL,
	STEP_REDIRECT,
	STEP_FORBIDDEN,
	STEP_RESET_OPEN,
	STEP_CHUNK_DROP,
	STEP_CHUNK_NO_END,
};

#define	RANGE_ANY	(-1)

struct http_step {
	enum http_step_kind kind;
	off_t len;		/* bytes sent, or STEP_OUTAGE duration */
	off_t range;		/* expected range start, 0 for none */
	const char *last_modified;
	const char *etag;		/* NULL: default strong ETag; "": omit */
	const char *if_range;	/* NULL: infer from the requested range */
	const char *date;		/* NULL: fixed date; "": omit */
	off_t size;		/* 0: SCRIPT_FILE_SIZE */
	int version;		/* distinct bytes for a replacement */
	bool ignore_condition;
	bool no_length;
	bool omit_validator;
	bool allow_ims;
	bool duplicate_etag;	/* send a second, different ETag */
};

#define	SCRIPT_FILE_SIZE	(64 * 1024)

static void
script_fill(char *buf, size_t len)
{
	for (size_t i = 0; i < len; i++)
		buf[i] = (char)((i * 7 + i / 251) & 0xff);
}

static void
script_serve(int listen_fd, const struct http_step *steps, size_t nsteps)
{
	static char body[SCRIPT_FILE_SIZE];
	struct linger lg = { .l_onoff = 1, .l_linger = 0 };
	char req[4096], hdr[512];
	const char *r;
	off_t start, len, size;
	size_t rlen;
	struct timespec ready, now;
	int cfd;

	signal(SIGPIPE, SIG_IGN);
	/* Never outlive a test which stopped making requests. */
	alarm(60);
	script_fill(body, sizeof(body));

	for (size_t i = 0; i < nsteps; i++) {
		const struct http_step *s = &steps[i];
		bool unavailable = false;
		const char *etag = s->etag != NULL ? s->etag : "\"original\"";
		const char *date = s->date != NULL ? s->date :
		    "Fri, 06 Nov 2026 00:00:00 GMT";
		const char *condition;
		char expected_header[512];

next_request:
		cfd = accept(listen_fd, NULL, NULL);
		if (cfd < 0)
			_exit(1);
		if (s->kind == STEP_UNEXPECTED)
			_exit(100 + (int)i);

		rlen = 0;
		for (;;) {
			ssize_t n = read(cfd, req + rlen, sizeof(req) - 1 - rlen);

			if (n <= 0)
				_exit(1);
			rlen += (size_t)n;
			req[rlen] = '\0';
			if (strstr(req, "\r\n\r\n") != NULL ||
			    rlen >= sizeof(req) - 1)
				break;
		}

		start = 0;
		if ((r = strstr(req, "\r\nRange: bytes=")) != NULL)
			start = strtoll(r + strlen("\r\nRange: bytes="), NULL,
			    10);
		if (s->range != RANGE_ANY && start != s->range)
			_exit(50 + (int)i);
		condition = s->if_range != NULL ? s->if_range :
		    (start > 0 ? "\"original\"" : "");
		r = strstr(req, "\r\nIf-Range:");
		if (*condition != '\0') {
			snprintf(expected_header, sizeof(expected_header),
			    "\r\nIf-Range: %s\r\n", condition);
			if (strstr(req, expected_header) == NULL)
				_exit(150 + (int)i);
		} else if (r != NULL) {
			_exit(150 + (int)i);
		}
		if (!s->allow_ims &&
		    strstr(req, "\r\nIf-Modified-Since:") != NULL)
			_exit(175 + (int)i);
		if (s->kind == STEP_FORBIDDEN) {
			const char reply[] = "HTTP/1.1 403 Forbidden\r\n"
			    "Content-Length: 0\r\nConnection: close\r\n\r\n";

			write(cfd, reply, sizeof(reply) - 1);
			close(cfd);
			continue;
		}
		if (s->kind == STEP_RATE_LIMIT) {
			const char reply[] = "HTTP/1.1 429 Too Many Requests\r\n"
			    "Content-Length: 0\r\nConnection: close\r\n\r\n";

			write(cfd, reply, sizeof(reply) - 1);
			close(cfd);
			continue;
		}
		if (s->kind == STEP_RESET_OPEN) {
			setsockopt(cfd, SOL_SOCKET, SO_LINGER, &lg, sizeof(lg));
			close(cfd);
			continue;
		}
		if (s->kind == STEP_BAD_RANGE) {
			const char reply[] = "HTTP/1.1 416 Range Not Satisfiable\r\n"
			    "Content-Range: bytes */20000\r\n"
			    "Content-Length: 0\r\nConnection: close\r\n\r\n";

			write(cfd, reply, sizeof(reply) - 1);
			close(cfd);
			continue;
		}
		if (s->kind == STEP_REDIRECT) {
			const char reply[] = "HTTP/1.1 302 Found\r\n"
			    "Location: /redirected\r\n"
			    "Content-Length: 0\r\nConnection: close\r\n\r\n";

			write(cfd, reply, sizeof(reply) - 1);
			close(cfd);
			continue;
		}
		if (s->kind == STEP_OUTAGE) {
			if (clock_gettime(CLOCK_MONOTONIC, &now) != 0)
				_exit(1);
			if (!unavailable) {
				ready = now;
				ready.tv_sec += s->len;
				unavailable = true;
			}
			if (now.tv_sec > ready.tv_sec ||
			    (now.tv_sec == ready.tv_sec &&
			    now.tv_nsec >= ready.tv_nsec))
				unavailable = false;
		}
		if (s->kind == STEP_RETRY || unavailable) {
			const char reply[] = "HTTP/1.1 503 Service Unavailable\r\n"
			    "Content-Length: 0\r\nConnection: close\r\n\r\n";

			write(cfd, reply, sizeof(reply) - 1);
			close(cfd);
			if (unavailable)
				goto next_request;
			continue;
		}

		if (s->kind == STEP_IGNORE_RANGE ||
		    (!s->ignore_condition && *condition != '\0' &&
		    strcmp(condition, *etag != '\0' ? etag :
		    (s->last_modified != NULL ? s->last_modified : "")) != 0))
			start = 0;
		size = s->size > 0 ? s->size : SCRIPT_FILE_SIZE;
		if (start >= size || size > SCRIPT_FILE_SIZE)
			_exit(1);
		script_fill(body, sizeof(body));
		for (size_t j = 0; j < sizeof(body); j++)
			body[j] ^= s->version;
		len = size - start;
		if (start > 0)
			snprintf(hdr, sizeof(hdr),
			    "HTTP/1.1 206 Partial Content\r\n"
			    "Content-Range: bytes %jd-%jd/%jd\r\n",
			    (intmax_t)start, (intmax_t)size - 1, (intmax_t)size);
		else
			snprintf(hdr, sizeof(hdr), "HTTP/1.1 200 OK\r\n");
		if (s->kind == STEP_CHUNK_DROP || s->kind == STEP_CHUNK_NO_END)
			snprintf(hdr + strlen(hdr), sizeof(hdr) - strlen(hdr),
			    "Transfer-Encoding: chunked\r\n");
		else if (!s->no_length)
			snprintf(hdr + strlen(hdr), sizeof(hdr) - strlen(hdr),
			    "Content-Length: %jd\r\n", (intmax_t)len);
		if (*etag != '\0' && !s->omit_validator)
			snprintf(hdr + strlen(hdr), sizeof(hdr) - strlen(hdr),
			    "ETag: %s\r\n", etag);
		if (s->duplicate_etag)
			snprintf(hdr + strlen(hdr), sizeof(hdr) - strlen(hdr),
			    "ETag: \"duplicate\"\r\n");
		if (*date != '\0')
			snprintf(hdr + strlen(hdr), sizeof(hdr) - strlen(hdr),
			    "Date: %s\r\n", date);
		if (s->last_modified != NULL && !s->omit_validator)
			snprintf(hdr + strlen(hdr), sizeof(hdr) - strlen(hdr),
			    "Last-Modified: %s\r\n", s->last_modified);
		snprintf(hdr + strlen(hdr), sizeof(hdr) - strlen(hdr),
		    "Connection: close\r\n\r\n");
		write(cfd, hdr, strlen(hdr));

		if (s->kind == STEP_CHUNK_DROP || s->kind == STEP_CHUNK_NO_END) {
			snprintf(hdr, sizeof(hdr), "%jx\r\n",
			    (uintmax_t)(s->kind == STEP_CHUNK_DROP ? len : s->len));
			write(cfd, hdr, strlen(hdr));
			write(cfd, body + start, s->len);
			if (s->kind == STEP_CHUNK_NO_END)
				write(cfd, "\r\n", 2);
			close(cfd);
			continue;
		}
		if ((s->kind == STEP_DROP || s->kind == STEP_RESET ||
		    s->kind == STEP_STALL) &&
		    s->len < len)
			len = s->len;
		if (len > 0)
			write(cfd, body + start, len);
		if (s->kind == STEP_STALL)
			sleep(2);
		if (s->kind == STEP_RESET) {
			/* Let pkg read what was sent before the reset. */
			usleep(200 * 1000);
			setsockopt(cfd, SOL_SOCKET, SO_LINGER, &lg, sizeof(lg));
		}
		close(cfd);
	}
	_exit(0);
}

static struct http_server
script_server_start(const struct http_step *steps, size_t nsteps)
{
	struct sockaddr_in addr;
	struct http_server srv;
	socklen_t addrlen;
	int listen_fd;

	listen_fd = socket(AF_INET, SOCK_STREAM, 0);
	ATF_REQUIRE_MSG(listen_fd != -1, "socket: %s", strerror(errno));
	memset(&addr, 0, sizeof(addr));
	addr.sin_family = AF_INET;
	addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	ATF_REQUIRE_MSG(bind(listen_fd, (struct sockaddr *)&addr,
	    sizeof(addr)) == 0, "bind: %s", strerror(errno));
	ATF_REQUIRE_MSG(listen(listen_fd, 4) == 0, "listen: %s",
	    strerror(errno));
	addrlen = sizeof(addr);
	ATF_REQUIRE_MSG(getsockname(listen_fd, (struct sockaddr *)&addr,
	    &addrlen) == 0, "getsockname: %s", strerror(errno));
	srv.port = ntohs(addr.sin_port);

	srv.pid = fork();
	ATF_REQUIRE_MSG(srv.pid != -1, "fork: %s", strerror(errno));
	if (srv.pid == 0)
		script_serve(listen_fd, steps, nsteps);
	close(listen_fd);

	return (srv);
}

/*
 * Stop the scripted server and return its exit status, or -1 when it had to
 * be killed: it was still waiting for a request, which is what a script
 * ending with STEP_UNEXPECTED expects.
 */
static int
script_server_stop(struct http_server *srv, bool kill_it)
{
	int status;

	if (kill_it)
		kill(srv->pid, SIGTERM);
	ATF_REQUIRE(waitpid(srv->pid, &status, 0) == srv->pid);
	if (WIFEXITED(status))
		return (WEXITSTATUS(status));
	return (-1);
}

/*
 * Fetch the scripted file through pkg_fetch_file_to_fd() and check the
 * outcome: the return code, the file received when it succeeded, and the
 * requests made (see script_serve()).
 */
static void
script_run_config(const struct http_step *steps, size_t nsteps,
    const char *retry, const char *delay, int expected_ret,
    off_t expected_size, off_t max_size, off_t initial_offset)
{
	char path[] = "/tmp/pkg_fetch_resume_XXXXXX";
	char expected[SCRIPT_FILE_SIZE], got[SCRIPT_FILE_SIZE + 1];
	char url[MAXPATHLEN];
	struct http_server srv;
	struct fetch_item fi = {0};
	struct stat st;
	bool trailing;
	ssize_t n;
	int fd, ret, status;

	signal(SIGPIPE, SIG_IGN);
	if (retry != NULL)
		ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY", retry, 1));
	ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY_DELAY", delay, 1));
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));

	srv = script_server_start(steps, nsteps);
	fd = mkstemp(path);
	ATF_REQUIRE_MSG(fd != -1, "mkstemp: %s", strerror(errno));
	unlink(path);
	ATF_REQUIRE(fcntl(fd, F_SETFL, O_APPEND) == 0);

	snprintf(url, sizeof(url), "http://127.0.0.1:%d/target", srv.port);
	fi.url = url;
	fi.expected_size = expected_size;
	fi.max_size = max_size;
	fi.offset = initial_offset;
	if (initial_offset > 0) {
		ATF_REQUIRE(ftruncate(fd, initial_offset) == 0);
		fi.mtime = 1;
	}
	ret = pkg_fetch_file_to_fd(NULL, fd, &fi, true);

	trailing = steps[nsteps - 1].kind == STEP_UNEXPECTED;
	status = script_server_stop(&srv, trailing);
	ATF_CHECK_EQ_MSG(trailing ? -1 : 0, status,
	    "unexpected requests: server status %d", status);
	ATF_REQUIRE_EQ_MSG(expected_ret, ret, "expected %d, got %d",
	    expected_ret, ret);

	if (ret == EPKG_OK) {
		const struct http_step *last = &steps[nsteps - (trailing ? 2 : 1)];
		off_t size = last->size > 0 ? last->size : SCRIPT_FILE_SIZE;

		script_fill(expected, sizeof(expected));
		for (size_t j = 0; j < sizeof(expected); j++)
			expected[j] ^= last->version;
		ATF_REQUIRE(fstat(fd, &st) == 0);
		ATF_REQUIRE_EQ_MSG(size, st.st_size,
		    "received %jd bytes", (intmax_t)st.st_size);
		n = pread(fd, got, sizeof(got), 0);
		ATF_REQUIRE_EQ(size, n);
		ATF_REQUIRE_MSG(memcmp(expected, got, size) == 0,
		    "received file differs from the served one");
	}
	close(fd);
	pkg_shutdown();
}

static void
script_run_delay(const struct http_step *steps, size_t nsteps,
    const char *retry, const char *delay, int expected_ret)
{
	script_run_config(steps, nsteps, retry, delay, expected_ret, 0, 0, 0);
}

static void
script_run(const struct http_step *steps, size_t nsteps, const char *retry,
    int expected_ret)
{
	script_run_delay(steps, nsteps, retry, "0", expected_ret);
}

ATF_TC_WITHOUT_HEAD(http_mirror_failover);
ATF_TC_WITHOUT_HEAD(http_mirror_all_dead);
ATF_TC_WITHOUT_HEAD(http_mirror_zero_retry);
ATF_TC_WITHOUT_HEAD(http_mirror_not_found);
ATF_TC_WITHOUT_HEAD(http_mirror_uptodate_mtime);
ATF_TC_WITHOUT_HEAD(http_mirror_uptodate_mtime_whitespace);
ATF_TC_WITHOUT_HEAD(http_mirror_uptodate_not_modified);
ATF_TC_WITHOUT_HEAD(http_retry_backoff);
ATF_TC_WITHOUT_HEAD(http_mirror_permanent);
ATF_TC_WITHOUT_HEAD(http_retry_permanent);
ATF_TC_WITHOUT_HEAD(http_mirror_permanent_transient);
ATF_TC_WITHOUT_HEAD(http_mirror_rounds);
ATF_TC_WITHOUT_HEAD(srv_mirror_rounds);
ATF_TC_WITHOUT_HEAD(srv_mirror_failover);
ATF_TC_WITHOUT_HEAD(http_mirror_one_round);
ATF_TC_WITHOUT_HEAD(http_mirror_negative_retry);
ATF_TC_WITHOUT_HEAD(http_retry_disabled_delay);
ATF_TC_WITHOUT_HEAD(http_retry_recovery);
ATF_TC_WITHOUT_HEAD(fetch_retry_delays);
ATF_TC_WITHOUT_HEAD(fetch_retry_interrupted_wait);
ATF_TC_WITHOUT_HEAD(http_resume_after_drop);
ATF_TC_WITHOUT_HEAD(http_resume_after_reset);
ATF_TC_WITHOUT_HEAD(http_resume_progress_bounded);
ATF_TC_WITHOUT_HEAD(http_resume_no_progress);
ATF_TC_WITHOUT_HEAD(http_resume_zero_retry);
ATF_TC_WITHOUT_HEAD(http_resume_range_ignored);
ATF_TC_WITHOUT_HEAD(http_resume_file_changed);
ATF_TC_WITHOUT_HEAD(http_resume_reconnect_budget);
ATF_TC_WITHOUT_HEAD(http_resume_reconnect_recovery);

/*
 * The first mirror is unreachable; try the second without any sleep, even
 * with a large configured delay. Exhausting the first mirror's budget
 * before failing over would needlessly delay a successful fetch.
 */
ATF_TC_BODY(http_mirror_failover, tc)
{
	char dir[] = "/tmp/pkg_http_mirror_XXXXXX";
	struct http_server srv;
	struct pkg_repo repo;
	struct fetch_item fi = {0};
	struct retry_trace trace = { .expected = "ff" };
	char alive_url[MAXPATHLEN];
	int ret;

	ATF_REQUIRE(mkdtemp(dir) != NULL);
	make_repo_file(dir, "target", "hello\n");

	srv = http_server_start(dir, HTTP_REPLY_OK, NULL);

	/* Ignore SIGPIPE like pkg does, so a write to a socket closed by
	 * the test HTTP server does not terminate the test case. */
	signal(SIGPIPE, SIG_IGN);

	ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY_DELAY", "60", 1));
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));
	retry_trace_start(&trace);

	repo = make_http_repo();
	pkg_repo_http_mirror_append(&repo, "http://127.0.0.1:1/", false);
	snprintf(alive_url, sizeof(alive_url), "http://127.0.0.1:%d/",
	    srv.port);
	pkg_repo_http_mirror_append(&repo, alive_url, true);

	fi.url = "http://pkg.test/target";

	ret = libfetch_open(&repo, &fi);
	ATF_REQUIRE_EQ_MSG(EPKG_OK, ret,
	    "failover to the second mirror failed: %d", ret);
	ATF_REQUIRE_MSG(repo.fh != NULL, "no fetch handle after success");
	retry_trace_stop(&trace);

	libfetch_cleanup(&repo);
	pkg_shutdown();

	http_server_stop(&srv);
	unlinkat(open(dir, O_DIRECTORY), "target", 0);
	rmdir(dir);
}

/*
 * Every mirror is unreachable; pkg must walk the whole list, give each
 * server its retry budget, then fail cleanly with EPKG_FATAL.
 */
ATF_TC_BODY(http_mirror_all_dead, tc)
{
	struct pkg_repo repo;
	struct fetch_item fi = {0};
	int ret;

	/* Fail over without waiting between the retries. */
	ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY_DELAY", "0", 1));
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));

	repo = make_http_repo();
	pkg_repo_http_mirror_append(&repo, "http://127.0.0.1:1/", false);
	pkg_repo_http_mirror_append(&repo, "http://127.0.0.1:2/", false);

	fi.url = "http://pkg.test/target";

	ret = libfetch_open(&repo, &fi);
	ATF_REQUIRE_EQ_MSG(EPKG_FATAL, ret,
	    "expected EPKG_FATAL when all mirrors are down, got %d", ret);
	ATF_REQUIRE_MSG(repo.fh == NULL, "handle should not be open on failure");

	libfetch_cleanup(&repo);
	pkg_shutdown();
}

/*
 * With FETCH_RETRY=0 only the first server is tried, without any sleep or
 * failover. A second mirror must not turn a disabled retry into another
 * attempt.
 */
ATF_TC_BODY(http_mirror_zero_retry, tc)
{
	struct pkg_repo repo;
	struct fetch_item fi = {0};
	struct retry_trace trace = { .expected = "f" };
	int ret;

	ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY", "0", 1));
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));
	retry_trace_start(&trace);

	repo = make_http_repo();
	pkg_repo_http_mirror_append(&repo, "http://127.0.0.1:1/", false);
	pkg_repo_http_mirror_append(&repo, "http://127.0.0.1:2/", false);

	fi.url = "http://pkg.test/target";

	ret = libfetch_open(&repo, &fi);
	ATF_REQUIRE_EQ_MSG(EPKG_FATAL, ret,
	    "expected EPKG_FATAL with FETCH_RETRY=0, got %d", ret);
	ATF_REQUIRE_MSG(repo.fh == NULL, "handle should not be open on failure");
	retry_trace_stop(&trace);

	libfetch_cleanup(&repo);
	pkg_shutdown();
}

/*
 * The mirror answers 404 for the requested document: libfetch_open() must
 * report EPKG_ENOENT and release the URL, whose document path still points
 * at the on-stack buffer of the mirror walk.
 */
ATF_TC_BODY(http_mirror_not_found, tc)
{
	struct http_server srv;
	struct pkg_repo repo;
	struct fetch_item fi = {0};
	char url[MAXPATHLEN];
	int ret;

	srv = http_server_start(NULL, HTTP_REPLY_NOT_FOUND, NULL);
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));

	repo = make_http_repo();
	repo.silent = true;
	snprintf(url, sizeof(url), "http://127.0.0.1:%d/", srv.port);
	pkg_repo_http_mirror_append(&repo, url, true);
	fi.url = "http://pkg.test/missing";

	ret = libfetch_open(&repo, &fi);
	ATF_REQUIRE_EQ_MSG(EPKG_ENOENT, ret, "expected EPKG_ENOENT, got %d",
	    ret);
	ATF_REQUIRE_MSG(repo.fh == NULL, "handle should not be open on failure");

	libfetch_cleanup(&repo);
	pkg_shutdown();
	http_server_stop(&srv);
}

/*
 * The mirror answers 200 to the conditional request but the document is
 * older than the requested mtime: libfetch_open() must report EPKG_UPTODATE
 * without leaving a handle open.
 */
static void
uptodate_mtime(const char *last_modified)
{
	char dir[] = "/tmp/pkg_http_mirror_XXXXXX";
	struct http_server srv;
	struct pkg_repo repo;
	struct fetch_item fi = {0};
	char url[MAXPATHLEN];
	int ret;

	ATF_REQUIRE(mkdtemp(dir) != NULL);
	make_repo_file(dir, "target", "hello\n");
	srv = http_server_start(dir, HTTP_REPLY_OK, last_modified);
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));

	repo = make_http_repo();
	snprintf(url, sizeof(url), "http://127.0.0.1:%d/", srv.port);
	pkg_repo_http_mirror_append(&repo, url, true);
	fi.url = "http://pkg.test/target";
	fi.mtime = time(NULL);

	ret = libfetch_open(&repo, &fi);
	ATF_REQUIRE_EQ_MSG(EPKG_UPTODATE, ret, "expected EPKG_UPTODATE, got %d",
	    ret);
	ATF_REQUIRE_MSG(repo.fh == NULL,
	    "handle should not be open when up to date");

	libfetch_cleanup(&repo);
	pkg_shutdown();
	http_server_stop(&srv);
	unlinkat(open(dir, O_DIRECTORY), "target", 0);
	rmdir(dir);
}

ATF_TC_BODY(http_mirror_uptodate_mtime, tc)
{
	uptodate_mtime("Wed, 01 Jan 2020 00:00:00 GMT");
}

/* Trailing whitespace is not part of the Last-Modified value. */
ATF_TC_BODY(http_mirror_uptodate_mtime_whitespace, tc)
{
	uptodate_mtime("Wed, 01 Jan 2020 00:00:00 GMT \t");
}

/*
 * The mirror answers 304: libfetch reports it as FETCH_OK without a handle,
 * so libfetch_open() must report EPKG_UPTODATE.
 */
ATF_TC_BODY(http_mirror_uptodate_not_modified, tc)
{
	struct http_server srv;
	struct pkg_repo repo;
	struct fetch_item fi = {0};
	char url[MAXPATHLEN];
	int ret;

	srv = http_server_start(NULL, HTTP_REPLY_NOT_MODIFIED, NULL);
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));

	repo = make_http_repo();
	snprintf(url, sizeof(url), "http://127.0.0.1:%d/", srv.port);
	pkg_repo_http_mirror_append(&repo, url, true);
	fi.url = "http://pkg.test/target";
	fi.mtime = time(NULL);

	ret = libfetch_open(&repo, &fi);
	ATF_REQUIRE_EQ_MSG(EPKG_UPTODATE, ret, "expected EPKG_UPTODATE, got %d",
	    ret);
	ATF_REQUIRE_MSG(repo.fh == NULL,
	    "handle should not be open when up to date");

	libfetch_cleanup(&repo);
	pkg_shutdown();
	http_server_stop(&srv);
}

/*
 * Retries against the same server are spaced out: FETCH_RETRY_DELAY, then
 * twice that, so FETCH_RETRY=3 against a dead server takes 1 + 2 seconds
 * instead of failing at once while e.g. the link is coming back up.
 */
ATF_TC_BODY(http_retry_backoff, tc)
{
	struct pkg_repo repo;
	struct fetch_item fi = {0};
	struct timespec t0, t1;
	double elapsed;
	int ret;

	ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY", "3", 1));
	ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY_DELAY", "1", 1));
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));

	repo = make_http_repo();
	repo.silent = true;
	pkg_repo_http_mirror_append(&repo, "http://127.0.0.1:1/", false);
	fi.url = "http://pkg.test/target";

	clock_gettime(CLOCK_MONOTONIC, &t0);
	ret = libfetch_open(&repo, &fi);
	clock_gettime(CLOCK_MONOTONIC, &t1);
	elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;

	ATF_REQUIRE_EQ_MSG(EPKG_FATAL, ret, "expected EPKG_FATAL, got %d", ret);
	ATF_REQUIRE_MSG(elapsed >= 2.9,
	    "3 attempts took %.2f seconds, expected about 3", elapsed);

	libfetch_cleanup(&repo);
	pkg_shutdown();
}

static struct dns_srvinfo *
srv_mirror(int port)
{
	struct dns_srvinfo *srv = calloc(1, sizeof(*srv));

	ATF_REQUIRE(srv != NULL);
	strlcpy(srv->host, "127.0.0.1", sizeof(srv->host));
	srv->port = port;
	return (srv);
}

/*
 * Check the entire sequence, including no sleep after the last failure.
 * Every request to the first server fails with first_kind, every request
 * to the second one with second_kind.
 */
static void
retry_script(mirror_t type, const char *retries, const char *delay,
    enum http_step_kind first_kind, enum http_step_kind second_kind,
    const char *expected)
{
	struct pkg_repo repo = make_http_repo();
	struct fetch_item fi = { .url = "http://pkg.test/target" };
	struct retry_trace trace = { .expected = expected };
	char url[MAXPATHLEN];
	const struct http_step first_steps[] = {
		{ .kind = first_kind },
		{ .kind = first_kind },
		{ .kind = first_kind },
		{ .kind = first_kind },
		{ .kind = first_kind },
		{ .kind = STEP_UNEXPECTED },
	};
	const struct http_step second_steps[] = {
		{ .kind = second_kind },
		{ .kind = second_kind },
		{ .kind = second_kind },
		{ .kind = second_kind },
		{ .kind = second_kind },
		{ .kind = STEP_UNEXPECTED },
	};
	struct http_server first, second;

	first = script_server_start(first_steps, NELEM(first_steps));
	second = script_server_start(second_steps, NELEM(second_steps));
	ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY", retries, 1));
	ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY_DELAY", delay, 1));
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));
	retry_trace_start(&trace);
	repo.mirror_type = type;
	repo.silent = true;
	if (type == HTTP) {
		snprintf(url, sizeof(url), "http://127.0.0.1:%d/a/", first.port);
		pkg_repo_http_mirror_append(&repo, url, true);
		snprintf(url, sizeof(url), "http://127.0.0.1:%d/b/", second.port);
		pkg_repo_http_mirror_append(&repo, url, true);
	} else if (type == SRV) {
		repo.srv = srv_mirror(first.port);
		repo.srv->next = srv_mirror(second.port);
	} else {
		snprintf(url, sizeof(url), "http://127.0.0.1:%d/a/target",
		    first.port);
		fi.url = repo.url = url;
	}
	ATF_REQUIRE_EQ(EPKG_FATAL, libfetch_open(&repo, &fi));
	retry_trace_stop(&trace);
	libfetch_cleanup(&repo);
	pkg_shutdown();
	ATF_REQUIRE_EQ(-1, script_server_stop(&first, true));
	ATF_REQUIRE_EQ(-1, script_server_stop(&second, true));
}

static void
retry_rounds(mirror_t type, const char *retries, const char *delay,
    const char *expected)
{
	retry_script(type, retries, delay, STEP_RETRY, STEP_RETRY, expected);
}

/*
 * Every mirror refuses the request (403): fail over within the pass, but
 * do not wait for a later pass that cannot succeed either.
 */
ATF_TC_BODY(http_mirror_permanent, tc)
{
	retry_script(HTTP, "5", "60", STEP_FORBIDDEN, STEP_FORBIDDEN, "ab");
}

ATF_TC_BODY(http_retry_permanent, tc)
{
	retry_script(NOMIRROR, "5", "60", STEP_FORBIDDEN, STEP_FORBIDDEN, "a");
}

/* One transient failure in a pass is enough to try another pass. */
ATF_TC_BODY(http_mirror_permanent_transient, tc)
{
	retry_script(HTTP, "2", "1", STEP_FORBIDDEN, STEP_RETRY, "abwab");
}

ATF_TC_BODY(http_mirror_rounds, tc)
{
	retry_rounds(HTTP, "3", "1", "abwabwab");
}

ATF_TC_BODY(srv_mirror_rounds, tc)
{
	retry_rounds(SRV, "3", "1", "ffwffwff");
}

ATF_TC_BODY(http_mirror_one_round, tc)
{
	retry_rounds(HTTP, "1", "60", "ab");
}

ATF_TC_BODY(http_mirror_negative_retry, tc)
{
	retry_rounds(HTTP, "-1", "60", "a");
}

ATF_TC_BODY(http_retry_disabled_delay, tc)
{
	retry_rounds(NOMIRROR, "5", "0", "aaaaa");
}

ATF_TC_BODY(srv_mirror_failover, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_RETRY, .allow_ims = true },
		{ .kind = STEP_UNEXPECTED },
	};
	struct http_server srv, dead;
	struct pkg_repo repo = make_http_repo();
	struct fetch_item fi = { .url = "http://pkg.test/target",
	    .mtime = 1 };
	struct retry_trace trace = { .expected = "ff" };

	dead = script_server_start(steps, NELEM(steps));
	srv = http_server_start(NULL, HTTP_REPLY_NOT_MODIFIED, NULL);
	ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY_DELAY", "60", 1));
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));
	retry_trace_start(&trace);
	repo.mirror_type = SRV;
	repo.srv = srv_mirror(dead.port);
	repo.srv->next = srv_mirror(srv.port);
	ATF_REQUIRE_EQ(EPKG_UPTODATE, libfetch_open(&repo, &fi));
	retry_trace_stop(&trace);
	libfetch_cleanup(&repo);
	pkg_shutdown();
	ATF_REQUIRE_EQ(-1, script_server_stop(&dead, true));
	http_server_stop(&srv);
}

/* Defaults must survive an outage longer than the old three-second window. */
ATF_TC_BODY(http_retry_recovery, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_OUTAGE, .len = 4 },
		{ .kind = STEP_UNEXPECTED },
	};

	ATF_REQUIRE_EQ(0, unsetenv("FETCH_RETRY"));
	ATF_REQUIRE_EQ(0, unsetenv("FETCH_RETRY_DELAY"));
	script_run_delay(steps, NELEM(steps), NULL, "1", EPKG_OK);
}

ATF_TC_BODY(fetch_retry_delays, tc)
{
	const struct {
		int64_t delay, attempt;
		unsigned int expected;
	} cases[] = {
		{ 1, 1, 1 }, { 1, 2, 2 }, { 1, 3, 4 }, { 1, 4, 8 },
		{ 1, 6, 32 }, { 1, 7, 60 }, { 1, INT64_MAX, 60 },
		{ 0, 1, 0 }, { -1, 1, 0 }, { INT64_MIN, 1, 0 },
		{ 1, 0, 0 }, { 1, INT64_MIN, 0 }, { 2, 3, 8 },
		{ 31, 2, 60 }, { 60, 1, 60 }, { 61, 1, 60 },
		{ INT64_MAX, 1, 60 }, { INT64_MAX, INT64_MAX, 60 },
	};

	for (size_t i = 0; i < NELEM(cases); i++)
		ATF_REQUIRE_EQ_MSG(cases[i].expected,
		    fetch_retry_delay(cases[i].delay, cases[i].attempt),
		    "unexpected delay for case %zu", i);
}

static volatile sig_atomic_t retry_signal;

static void
retry_signal_handler(int sig)
{
	retry_signal = sig;
}

ATF_TC_BODY(fetch_retry_interrupted_wait, tc)
{
	struct sigaction sa = { .sa_handler = retry_signal_handler }, old;
	struct itimerval timer = { .it_value.tv_usec = 100000 };
	struct timespec t0, t1;
	double elapsed;

	sigemptyset(&sa.sa_mask);
	ATF_REQUIRE(sigaction(SIGALRM, &sa, &old) == 0);
	ATF_REQUIRE_EQ(0, setenv("FETCH_RETRY_DELAY", "1", 1));
	ATF_REQUIRE_EQ(EPKG_OK, pkg_ini(NULL, NULL, 0));
	ATF_REQUIRE(clock_gettime(CLOCK_MONOTONIC, &t0) == 0);
	ATF_REQUIRE(setitimer(ITIMER_REAL, &timer, NULL) == 0);
	fetch_retry_wait(1);
	ATF_REQUIRE(clock_gettime(CLOCK_MONOTONIC, &t1) == 0);
	elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
	ATF_REQUIRE_EQ(SIGALRM, retry_signal);
	ATF_REQUIRE_MSG(elapsed >= 0.99, "wait interrupted after %.2fs", elapsed);
	ATF_REQUIRE(sigaction(SIGALRM, &old, NULL) == 0);
	pkg_shutdown();
}

/*
 * The connection is closed a sixth of the way through: pkg must ask for the
 * rest of the file only, and end up with the whole file.  Before, the fetch
 * failed outright ("fetch size does not match expected package size"), or
 * silently returned a truncated file when no size was expected.
 */
ATF_TC_BODY(http_resume_after_drop, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_SERVE, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), NULL, EPKG_OK);
}

/*
 * The connection is reset mid-transfer, a read error rather than an early
 * end of file ("An error occurred while fetching package" before): it is
 * resumed the same way.
 */
ATF_TC_BODY(http_resume_after_reset, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_RESET, .len = 10000 },
		{ .kind = STEP_SERVE, .range = RANGE_ANY },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), NULL, EPKG_OK);
}

/* Progress does not replenish the total recovery budget. */
ATF_TC_BODY(http_resume_progress_bounded, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_DROP, .len = 10000, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_FATAL);
}

/*
 * After the first interruption no more data comes: with FETCH_RETRY=2 pkg
 * resumes twice, then gives up without a further request.
 */
ATF_TC_BODY(http_resume_no_progress, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_DROP, .range = 10000 },
		{ .kind = STEP_DROP, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_FATAL);
}

/* FETCH_RETRY=0 disables resuming too. */
ATF_TC_BODY(http_resume_zero_retry, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "0", EPKG_FATAL);
}

/*
 * The server answers the range request with the whole file: what was
 * already received must be dropped rather than kept in front of it.
 */
ATF_TC_BODY(http_resume_range_ignored, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_IGNORE_RANGE, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), NULL, EPKG_OK);
}

/*
 * The file changed on the server between the interruption and the resumed
 * request (its Last-Modified differs): the parts would not match, so pkg
 * must start over from the beginning.
 */
ATF_TC_BODY(http_resume_file_changed, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .etag = "",
		  .last_modified = "Wed, 01 Jan 2025 00:00:00 GMT" },
		{ .kind = STEP_SERVE, .range = 10000, .etag = "",
		  .if_range = "Wed, 01 Jan 2025 00:00:00 GMT",
		  .last_modified = "Thu, 02 Jan 2025 00:00:00 GMT",
		  .ignore_condition = true, .version = 1 },
		{ .kind = STEP_SERVE, .etag = "", .version = 1,
		  .last_modified = "Thu, 02 Jan 2025 00:00:00 GMT" },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

/* Failed reconnections must not each start another FETCH_RETRY budget. */
ATF_TC_BODY(http_resume_reconnect_budget, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_RETRY, .range = 10000 },
		{ .kind = STEP_RETRY, .range = 10000 },
		{ .kind = STEP_RETRY, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "3", EPKG_FATAL);
}

ATF_TC_BODY(http_resume_reconnect_recovery, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_RETRY, .range = 10000 },
		{ .kind = STEP_SERVE, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

/* A 429 while reconnecting is retried, as it is when opening. */
ATF_TC_WITHOUT_HEAD(http_resume_reconnect_unknown);
ATF_TC_BODY(http_resume_reconnect_unknown, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_RATE_LIMIT, .range = 10000 },
		{ .kind = STEP_SERVE, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_etag_changed);
ATF_TC_BODY(http_resume_etag_changed, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_SERVE, .range = 10000,
		  .etag = "\"replacement\"", .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_invalid_validator);
ATF_TC_BODY(http_resume_invalid_validator, tc)
{
	/* Reject a 206 whose ETag contradicts If-Range before writing it. */
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_SERVE, .range = 10000,
		  .etag = "\"replacement\"", .version = 1,
		  .ignore_condition = true },
		{ .kind = STEP_SERVE, .etag = "\"replacement\"", .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_no_validator);
ATF_TC_BODY(http_resume_no_validator, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .etag = "" },
		{ .kind = STEP_SERVE, .etag = "", .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_weak_etag);
ATF_TC_BODY(http_resume_weak_etag, tc)
{
	/* A weak ETag also prevents falling back to Last-Modified. */
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .etag = "W/\"original\"",
		  .last_modified = "Wed, 01 Jan 2025 00:00:00 GMT" },
		{ .kind = STEP_SERVE, .etag = "W/\"replacement\"", .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_weak_date);
ATF_TC_BODY(http_resume_weak_date, tc)
{
	/* Last-Modified alone is not proof of byte-for-byte identity. */
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .etag = "",
		  .date = "Wed, 01 Jan 2025 00:00:30 GMT",
		  .last_modified = "Wed, 01 Jan 2025 00:00:00 GMT" },
		{ .kind = STEP_SERVE, .etag = "", .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_date_validator);
ATF_TC_BODY(http_resume_date_validator, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .etag = "",
		  .date = "Wed, 01 Jan 2025 00:01:00 GMT",
		  .last_modified = "Wed, 01 Jan 2025 00:00:00 GMT" },
		{ .kind = STEP_SERVE, .range = 10000, .etag = "",
		  .if_range = "Wed, 01 Jan 2025 00:00:00 GMT",
		  .last_modified = "Wed, 01 Jan 2025 00:00:00 GMT" },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_restart_interrupted);
ATF_TC_BODY(http_resume_restart_interrupted, tc)
{
	/* Replacement B is interrupted below A's old high-water offset. */
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 50000 },
		{ .kind = STEP_DROP, .len = 10000, .range = 50000,
		  .etag = "\"replacement\"", .version = 1 },
		{ .kind = STEP_SERVE, .range = 10000,
		  .if_range = "\"replacement\"",
		  .etag = "\"replacement\"", .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_shrunk);
ATF_TC_BODY(http_resume_shrunk, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 50000 },
		{ .kind = STEP_BAD_RANGE, .range = 50000 },
		{ .kind = STEP_SERVE, .size = 20000, .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_restart_bounded);
ATF_TC_BODY(http_resume_restart_bounded, tc)
{
	/* Even the full GET after a 416 must consume a recovery attempt. */
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 50000 },
		{ .kind = STEP_BAD_RANGE, .range = 50000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_FATAL);
}

ATF_TC_WITHOUT_HEAD(http_resume_redirect);
ATF_TC_BODY(http_resume_redirect, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_REDIRECT, .range = 10000 },
		{ .kind = STEP_SERVE, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_stall);
ATF_TC_BODY(http_resume_stall, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_STALL, .len = 10000 },
		{ .kind = STEP_SERVE, .range = RANGE_ANY },
		{ .kind = STEP_UNEXPECTED },
	};

	ATF_REQUIRE_EQ(0, setenv("FETCH_TIMEOUT", "1", 1));
	script_run_delay(steps, NELEM(steps), "2", "1", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_unknown_length);
ATF_TC_BODY(http_resume_unknown_length, tc)
{
	/* The caller's expected size detects early EOF without Content-Length. */
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .no_length = true },
		{ .kind = STEP_SERVE, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run_config(steps, NELEM(steps), "1", "0", EPKG_OK,
	    SCRIPT_FILE_SIZE, 0, 0);
}

ATF_TC_WITHOUT_HEAD(http_resume_size_limit);
ATF_TC_BODY(http_resume_size_limit, tc)
{
	/* A replacement discovered during recovery cannot bypass max_size. */
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .size = 20000 },
		{ .kind = STEP_SERVE, .range = 10000,
		  .etag = "\"replacement\"", .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run_config(steps, NELEM(steps), "1", "0", EPKG_FATAL, 0, 30000, 0);
}

ATF_TC_WITHOUT_HEAD(http_resume_expected_size);
ATF_TC_BODY(http_resume_expected_size, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .size = 20000 },
		{ .kind = STEP_SERVE, .range = 10000,
		  .etag = "\"replacement\"", .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run_config(steps, NELEM(steps), "1", "0", EPKG_FATAL, 20000, 0, 0);
}

static int
cancel_progress(void *data, struct pkg_event *ev)
{
	(void)data;
	return (ev->type == PKG_EVENT_PROGRESS_TICK);
}

ATF_TC_WITHOUT_HEAD(http_resume_oversized_etag);
ATF_TC_BODY(http_resume_oversized_etag, tc)
{
	char etag[300];
	struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .etag = etag },
		{ .kind = STEP_SERVE, .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	memset(etag, 'a', sizeof(etag));
	etag[0] = etag[sizeof(etag) - 2] = '"';
	etag[sizeof(etag) - 1] = '\0';
	script_run(steps, NELEM(steps), "1", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_malformed_etag);
ATF_TC_BODY(http_resume_malformed_etag, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .etag = "not-quoted" },
		{ .kind = STEP_SERVE, .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_validator_omitted);
ATF_TC_BODY(http_resume_validator_omitted, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_DROP, .len = 10000, .range = 10000,
		  .omit_validator = true },
		{ .kind = STEP_SERVE, .range = 20000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

/*
 * Two ETags leave no validator: the response is still accepted, but the
 * interrupted transfer restarts without a range, and without falling back
 * to the otherwise eligible Last-Modified date.
 */
ATF_TC_WITHOUT_HEAD(http_resume_duplicate_etag);
ATF_TC_BODY(http_resume_duplicate_etag, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .duplicate_etag = true,
		  .last_modified = "Wed, 01 Jan 2025 00:00:00 GMT" },
		{ .kind = STEP_SERVE, .duplicate_etag = true,
		  .last_modified = "Wed, 01 Jan 2025 00:00:00 GMT" },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

/*
 * Trailing whitespace after Last-Modified and Date is not part of their
 * values: the date still validates the range, and is sent back without it.
 */
ATF_TC_WITHOUT_HEAD(http_resume_date_whitespace);
ATF_TC_BODY(http_resume_date_whitespace, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .etag = "",
		  .last_modified = "Wed, 01 Jan 2025 00:00:00 GMT \t",
		  .date = "Fri, 06 Nov 2026 00:00:00 GMT " },
		{ .kind = STEP_SERVE, .range = 10000, .etag = "",
		  .if_range = "Wed, 01 Jan 2025 00:00:00 GMT",
		  .last_modified = "Wed, 01 Jan 2025 00:00:00 GMT ",
		  .ignore_condition = true },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_etag_whitespace);
ATF_TC_BODY(http_resume_etag_whitespace, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000, .etag = "\"original\" " },
		{ .kind = STEP_SERVE, .range = 10000, .etag = "\"original\"\t",
		  .if_range = "\"original\"", .ignore_condition = true },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_forbidden);
ATF_TC_BODY(http_resume_forbidden, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_FORBIDDEN, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "5", EPKG_FATAL);
}

ATF_TC_WITHOUT_HEAD(http_resume_reset_open);
ATF_TC_BODY(http_resume_reset_open, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_DROP, .len = 10000 },
		{ .kind = STEP_RESET_OPEN, .range = 10000 },
		{ .kind = STEP_SERVE, .range = 10000 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "2", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_old_partial);
ATF_TC_BODY(http_resume_old_partial, tc)
{
	/* A previous invocation's bytes have no stored HTTP validator. */
	const struct http_step steps[] = {
		{ .kind = STEP_SERVE, .version = 1 },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run_config(steps, NELEM(steps), "1", "0", EPKG_OK,
	    0, 0, 10000);
}

ATF_TC_WITHOUT_HEAD(http_resume_cancel);
ATF_TC_BODY(http_resume_cancel, tc)
{
	const struct http_step steps[] = {
		{ .kind = STEP_SERVE },
		{ .kind = STEP_UNEXPECTED },
	};

	pkg_event_register(cancel_progress, NULL);
	script_run(steps, NELEM(steps), "5", EPKG_CANCEL);
	pkg_event_register(NULL, NULL);
}

ATF_TC_WITHOUT_HEAD(http_resume_chunk_drop);
ATF_TC_BODY(http_resume_chunk_drop, tc)
{
	/* No Content-Length or expected size: chunk framing detects the EOF. */
	const struct http_step steps[] = {
		{ .kind = STEP_CHUNK_DROP, .len = 10000 },
		{ .kind = STEP_SERVE, .range = RANGE_ANY },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_OK);
}

ATF_TC_WITHOUT_HEAD(http_resume_chunk_no_end);
ATF_TC_BODY(http_resume_chunk_no_end, tc)
{
	/* No Content-Length or expected size: chunk framing detects the EOF. */
	const struct http_step steps[] = {
		{ .kind = STEP_CHUNK_NO_END, .len = 10000 },
		{ .kind = STEP_SERVE, .range = RANGE_ANY },
		{ .kind = STEP_UNEXPECTED },
	};

	script_run(steps, NELEM(steps), "1", EPKG_OK);
}

ATF_TP_ADD_TCS(tp)
{
	ATF_TP_ADD_TC(tp, http_mirror_failover);
	ATF_TP_ADD_TC(tp, http_mirror_all_dead);
	ATF_TP_ADD_TC(tp, http_mirror_zero_retry);
	ATF_TP_ADD_TC(tp, http_mirror_not_found);
	ATF_TP_ADD_TC(tp, http_mirror_uptodate_mtime);
	ATF_TP_ADD_TC(tp, http_mirror_uptodate_mtime_whitespace);
	ATF_TP_ADD_TC(tp, http_mirror_uptodate_not_modified);
	ATF_TP_ADD_TC(tp, http_retry_backoff);
	ATF_TP_ADD_TC(tp, http_mirror_permanent);
	ATF_TP_ADD_TC(tp, http_retry_permanent);
	ATF_TP_ADD_TC(tp, http_mirror_permanent_transient);
	ATF_TP_ADD_TC(tp, http_mirror_rounds);
	ATF_TP_ADD_TC(tp, srv_mirror_rounds);
	ATF_TP_ADD_TC(tp, srv_mirror_failover);
	ATF_TP_ADD_TC(tp, http_mirror_one_round);
	ATF_TP_ADD_TC(tp, http_mirror_negative_retry);
	ATF_TP_ADD_TC(tp, http_retry_disabled_delay);
	ATF_TP_ADD_TC(tp, http_retry_recovery);
	ATF_TP_ADD_TC(tp, fetch_retry_delays);
	ATF_TP_ADD_TC(tp, fetch_retry_interrupted_wait);
	ATF_TP_ADD_TC(tp, http_resume_after_drop);
	ATF_TP_ADD_TC(tp, http_resume_after_reset);
	ATF_TP_ADD_TC(tp, http_resume_progress_bounded);
	ATF_TP_ADD_TC(tp, http_resume_no_progress);
	ATF_TP_ADD_TC(tp, http_resume_zero_retry);
	ATF_TP_ADD_TC(tp, http_resume_range_ignored);
	ATF_TP_ADD_TC(tp, http_resume_file_changed);
	ATF_TP_ADD_TC(tp, http_resume_reconnect_budget);
	ATF_TP_ADD_TC(tp, http_resume_reconnect_recovery);
	ATF_TP_ADD_TC(tp, http_resume_reconnect_unknown);

	ATF_TP_ADD_TC(tp, http_resume_etag_changed);
	ATF_TP_ADD_TC(tp, http_resume_invalid_validator);
	ATF_TP_ADD_TC(tp, http_resume_no_validator);
	ATF_TP_ADD_TC(tp, http_resume_weak_etag);
	ATF_TP_ADD_TC(tp, http_resume_weak_date);
	ATF_TP_ADD_TC(tp, http_resume_date_validator);
	ATF_TP_ADD_TC(tp, http_resume_restart_interrupted);
	ATF_TP_ADD_TC(tp, http_resume_shrunk);
	ATF_TP_ADD_TC(tp, http_resume_restart_bounded);
	ATF_TP_ADD_TC(tp, http_resume_redirect);
	ATF_TP_ADD_TC(tp, http_resume_stall);
	ATF_TP_ADD_TC(tp, http_resume_unknown_length);
	ATF_TP_ADD_TC(tp, http_resume_size_limit);
	ATF_TP_ADD_TC(tp, http_resume_expected_size);

	ATF_TP_ADD_TC(tp, http_resume_oversized_etag);
	ATF_TP_ADD_TC(tp, http_resume_malformed_etag);
	ATF_TP_ADD_TC(tp, http_resume_validator_omitted);
	ATF_TP_ADD_TC(tp, http_resume_duplicate_etag);
	ATF_TP_ADD_TC(tp, http_resume_date_whitespace);
	ATF_TP_ADD_TC(tp, http_resume_etag_whitespace);
	ATF_TP_ADD_TC(tp, http_resume_forbidden);
	ATF_TP_ADD_TC(tp, http_resume_reset_open);
	ATF_TP_ADD_TC(tp, http_resume_old_partial);
	ATF_TP_ADD_TC(tp, http_resume_cancel);

	ATF_TP_ADD_TC(tp, http_resume_chunk_drop);
	ATF_TP_ADD_TC(tp, http_resume_chunk_no_end);

	return (atf_no_error());
}
