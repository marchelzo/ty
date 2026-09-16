import base64
import http.server
import os
import pathlib
import subprocess
import sys
import tempfile
import threading
import urllib.parse


ROOT = pathlib.Path(__file__).resolve().parents[3]
TOKEN = base64.b64encode(b'ty:secret').decode()


class GitServer(http.server.BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        pass

    def do_GET(self):
        self.serve_git()

    def do_POST(self):
        self.serve_git()

    def read_body(self):
        if self.headers.get('Transfer-Encoding') != 'chunked':
            return self.rfile.read(int(self.headers.get('Content-Length', '0')))

        chunks = []
        while True:
            size = int(self.rfile.readline().split(b';', 1)[0], 16)
            if size == 0:
                self.rfile.readline()
                return b''.join(chunks)
            chunks.append(self.rfile.read(size))
            self.rfile.read(2)

    def serve_git(self):
        if self.headers.get('Authorization') != f'Basic {TOKEN}':
            self.send_response(401)
            self.send_header('WWW-Authenticate', 'Basic realm="ty-git"')
            self.send_header('Content-Length', '0')
            self.end_headers()
            return

        url = urllib.parse.urlsplit(self.path)
        body = self.read_body()
        env = {
            **os.environ,
            'GIT_PROJECT_ROOT': self.server.git_root,
            'GIT_HTTP_EXPORT_ALL': '1',
            'PATH_INFO': url.path,
            'QUERY_STRING': url.query,
            'REQUEST_METHOD': self.command,
            'CONTENT_TYPE': self.headers.get('Content-Type', ''),
            'CONTENT_LENGTH': str(len(body)),
            'REMOTE_USER': 'ty',
        }
        response = subprocess.run(
            ['git', 'http-backend'],
            input=body,
            capture_output=True,
            check=True,
            env=env,
        )
        headers, body = response.stdout.split(b'\r\n\r\n', 1)
        self.send_response(200)
        for line in headers.decode().split('\r\n'):
            key, value = line.split(':', 1)
            self.send_header(key, value.strip())
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def main():
    with tempfile.TemporaryDirectory(prefix='ty-git-http-') as directory:
        remote = pathlib.Path(directory) / 'remote.git'
        subprocess.run(
            ['git', 'init', '--bare', '--initial-branch=main', str(remote)],
            check=True,
            capture_output=True,
        )
        subprocess.run(
            ['git', '-C', str(remote), 'config', 'http.receivepack', 'true'],
            check=True,
        )
        subprocess.run(
            ['git', '-C', str(remote), 'config', 'receive.denyNonFastForwards', 'true'],
            check=True,
        )
        server = http.server.ThreadingHTTPServer(('127.0.0.1', 0), GitServer)
        server.git_root = directory
        worker = threading.Thread(target=server.serve_forever, daemon=True)
        worker.start()
        port = server.server_port
        try:
            subprocess.run(
                [str(ROOT / 'ty'), *sys.argv[1:], '--test', 'tests/fixtures/git/auth.ty'],
                cwd=ROOT,
                check=True,
                timeout=30,
                env={
                    **os.environ,
                    'TY_GIT_AUTH_URL': f'http://127.0.0.1:{port}/remote.git',
                },
            )
        finally:
            server.shutdown()
            server.server_close()
            worker.join()


if __name__ == '__main__':
    main()
