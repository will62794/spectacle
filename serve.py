import http.server
import socketserver
import os
import json
import argparse

#
# Starts a local server to serve the Spectacle app but also allows for serving of local spec files
# by passing a directory for these to be served from and automatically detected by the app, for interacting
# with specs from locally defined files e.g.
#
# python3 serve.py --local_dir /path/to/local/specs/dir
#

# Parse command line arguments
parser = argparse.ArgumentParser()
parser.add_argument('--local_dir', type=str, help='Path to local data directory containing TLA+ files', default=None)
args = parser.parse_args()

class MultiDirHandler(http.server.SimpleHTTPRequestHandler):
    # map URL prefix → local directory
    roots = {
        "/static": "/path/to/static",
        "/local_dir": args.local_dir
    }

    def do_GET(self):
        if self.path == "/api/local_dir_files" and args.local_dir is not None:
            # Get list of .tla files in local_data directory
            local_data_dir = self.roots["/local_dir"]
            tla_files = []
            for root, dirs, files in os.walk(local_data_dir):
                for file in files:
                    if file.endswith(".tla"):
                        rel_path = os.path.relpath(os.path.join(root, file), local_data_dir)
                        tla_files.append(rel_path)

            # Send JSON response
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({"tla_files": tla_files}).encode())
            return

        return super().do_GET()

    def translate_path(self, path):
        for prefix, root in self.roots.items():
            if path.startswith(prefix):
                # strip prefix and join with root dir
                rel = path[len(prefix):].lstrip("/")
                return os.path.join(root, rel)
        # fallback: default directory
        return http.server.SimpleHTTPRequestHandler.translate_path(self, path)

PORT = 9000
with socketserver.TCPServer(("", PORT), MultiDirHandler) as httpd:
    print(f"Serving at port {PORT}")
    httpd.serve_forever()