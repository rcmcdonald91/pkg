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
 * A scripted server for the retry tests: it answers one request
 * per step, in order, each time with the rest of the file from the offset
 * of the request's range (the whole file when there is none), and exits 0
 * once every step was served.  It exits with 50 + step when a request does
 * not ask for the expected range, and with 100 + step on a request reaching
 * a STEP_UNEXPECTED step, so the test can tell exactly which requests pkg
 * made.
 */
enum http_step_kind {
	/* Send the rest of the file. */
	STEP_SERVE,
	/* Fail to reopen the transfer with a retryable HTTP error. */
	STEP_RETRY,
	/* Return 503 for len seconds from the first request, then serve. */
	STEP_OUTAGE,
	/* pkg must not make this request. */
	STEP_UNEXPECTED,
	/* Refuse the request with 403 Forbidden. */
	STEP_FORBIDDEN,
};

#define	RANGE_ANY	(-1)

struct http_step {
	enum http_step_kind kind;
	off_t len;		/* bytes sent, or STEP_OUTAGE duration */
	off_t range;		/* expected range start, 0 for none */
	const char *last_modified;
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
	char req[4096], hdr[512];
	const char *r;
	off_t start, len;
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
		if (start >= SCRIPT_FILE_SIZE)
			_exit(1);
		if (s->kind == STEP_FORBIDDEN) {
			const char reply[] = "HTTP/1.1 403 Forbidden\r\n"
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

		len = SCRIPT_FILE_SIZE - start;
		if (start > 0)
			snprintf(hdr, sizeof(hdr),
			    "HTTP/1.1 206 Partial Content\r\n"
			    "Content-Range: bytes %jd-%d/%d\r\n",
			    (intmax_t)start, SCRIPT_FILE_SIZE - 1,
			    SCRIPT_FILE_SIZE);
		else
			snprintf(hdr, sizeof(hdr), "HTTP/1.1 200 OK\r\n");
		snprintf(hdr + strlen(hdr), sizeof(hdr) - strlen(hdr),
		    "Content-Length: %jd\r\n", (intmax_t)len);
		if (s->last_modified != NULL)
			snprintf(hdr + strlen(hdr), sizeof(hdr) - strlen(hdr),
			    "Last-Modified: %s\r\n", s->last_modified);
		snprintf(hdr + strlen(hdr), sizeof(hdr) - strlen(hdr),
		    "Connection: close\r\n\r\n");
		write(cfd, hdr, strlen(hdr));

		if (len > 0)
			write(cfd, body + start, len);
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
script_run_delay(const struct http_step *steps, size_t nsteps,
    const char *retry, const char *delay, int expected_ret)
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

	snprintf(url, sizeof(url), "http://127.0.0.1:%d/target", srv.port);
	fi.url = url;
	ret = pkg_fetch_file_to_fd(NULL, fd, &fi, true);

	trailing = steps[nsteps - 1].kind == STEP_UNEXPECTED;
	status = script_server_stop(&srv, trailing);
	ATF_CHECK_EQ_MSG(trailing ? -1 : 0, status,
	    "unexpected requests: server status %d", status);
	ATF_REQUIRE_EQ_MSG(expected_ret, ret, "expected %d, got %d",
	    expected_ret, ret);

	if (ret == EPKG_OK) {
		script_fill(expected, sizeof(expected));
		ATF_REQUIRE(fstat(fd, &st) == 0);
		ATF_REQUIRE_EQ_MSG(SCRIPT_FILE_SIZE, st.st_size,
		    "received %jd bytes", (intmax_t)st.st_size);
		n = pread(fd, got, sizeof(got), 0);
		ATF_REQUIRE_EQ(SCRIPT_FILE_SIZE, n);
		ATF_REQUIRE_MSG(memcmp(expected, got, SCRIPT_FILE_SIZE) == 0,
		    "received file differs from the served one");
	}
	close(fd);
	pkg_shutdown();
}

ATF_TC_WITHOUT_HEAD(http_mirror_failover);
ATF_TC_WITHOUT_HEAD(http_mirror_all_dead);
ATF_TC_WITHOUT_HEAD(http_mirror_zero_retry);
ATF_TC_WITHOUT_HEAD(http_mirror_not_found);
ATF_TC_WITHOUT_HEAD(http_mirror_uptodate_mtime);
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
ATF_TC_BODY(http_mirror_uptodate_mtime, tc)
{
	char dir[] = "/tmp/pkg_http_mirror_XXXXXX";
	struct http_server srv;
	struct pkg_repo repo;
	struct fetch_item fi = {0};
	char url[MAXPATHLEN];
	int ret;

	ATF_REQUIRE(mkdtemp(dir) != NULL);
	make_repo_file(dir, "target", "hello\n");
	srv = http_server_start(dir, HTTP_REPLY_OK,
	    "Wed, 01 Jan 2020 00:00:00 GMT");
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
		{ first_kind, 0, 0, NULL },
		{ first_kind, 0, 0, NULL },
		{ first_kind, 0, 0, NULL },
		{ first_kind, 0, 0, NULL },
		{ first_kind, 0, 0, NULL },
		{ STEP_UNEXPECTED, 0, 0, NULL },
	};
	const struct http_step second_steps[] = {
		{ second_kind, 0, 0, NULL },
		{ second_kind, 0, 0, NULL },
		{ second_kind, 0, 0, NULL },
		{ second_kind, 0, 0, NULL },
		{ second_kind, 0, 0, NULL },
		{ STEP_UNEXPECTED, 0, 0, NULL },
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
		{ STEP_RETRY, 0, 0, NULL },
		{ STEP_UNEXPECTED, 0, 0, NULL },
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
		{ STEP_OUTAGE, 4, 0, NULL },
		{ STEP_UNEXPECTED, 0, 0, NULL },
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

ATF_TP_ADD_TCS(tp)
{
	ATF_TP_ADD_TC(tp, http_mirror_failover);
	ATF_TP_ADD_TC(tp, http_mirror_all_dead);
	ATF_TP_ADD_TC(tp, http_mirror_zero_retry);
	ATF_TP_ADD_TC(tp, http_mirror_not_found);
	ATF_TP_ADD_TC(tp, http_mirror_uptodate_mtime);
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

	return (atf_no_error());
}
