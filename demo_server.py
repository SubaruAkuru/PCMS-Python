# -*- coding: utf-8 -*-
"""
demo_server.py —— 网页版亲属计算器的本地服务器（纯标准库）。

用法：
    python demo_server.py [端口]     # 默认 8756
然后浏览器打开 http://127.0.0.1:8756/demo/index.html

也可以直接用浏览器打开 demo/index.html（离线可用，无需服务器）。
"""
import functools
import http.server
import os
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))
PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8756


class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=ROOT, **kwargs)

    def end_headers(self):
        self.send_header('Cache-Control', 'no-store')
        super().end_headers()

    def log_message(self, fmt, *args):
        sys.stderr.write('%s - %s\n' % (self.address_string(), fmt % args))


if __name__ == '__main__':
    server = http.server.ThreadingHTTPServer(('127.0.0.1', PORT), Handler)
    print(f'亲属计算器 demo 已启动： http://127.0.0.1:{PORT}/demo/index.html  (Ctrl+C 停止)')
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
