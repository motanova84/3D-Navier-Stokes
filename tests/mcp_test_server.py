#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Servidor MCP de prueba - network.checkResonance (Nivel B)."""

import json
import sys
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from mcp_network.resonance import check_node_resonance


class MCPTestHandler(BaseHTTPRequestHandler):
    def do_POST(self) -> None:  # noqa: N802
        if self.path != "/jsonrpc":
            self.send_error(404)
            return

        content_length = int(self.headers["Content-Length"])
        post_data = self.rfile.read(content_length)
        request = json.loads(post_data)

        if request.get("method") == "network.checkResonance":
            node = request.get("params", {}).get("node")
            result = check_node_resonance(node)
            response = {
                "jsonrpc": "2.0",
                "id": request.get("id"),
                "result": result,
            }
        else:
            response = {
                "jsonrpc": "2.0",
                "id": request.get("id"),
                "error": {"code": -32601, "message": "Method not found"},
            }

        body = json.dumps(response).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


if __name__ == "__main__":
    port = 8506
    server = HTTPServer(("127.0.0.1", port), MCPTestHandler)
    print(f"🚀 MCP Test Server escuchando en http://127.0.0.1:{port}/jsonrpc")
    print("Método expuesto: network.checkResonance")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nServidor detenido.")
