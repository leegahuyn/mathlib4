from __future__ import annotations

import json
import os
import queue
import subprocess
import threading
import time
from pathlib import Path
from typing import Any

import fa418_lsp_strict_tournament as base


class FixedLeanLsp(base.LeanLsp):
    def __init__(self, root: Path, stderr_path: Path) -> None:
        self.root = root.resolve()
        self.proc = subprocess.Popen(
            [
                "lake",
                "env",
                "lean",
                "-DwarningAsError=false",
                "-DmaxErrors=200",
                "--server",
            ],
            cwd=self.root,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
        )
        assert self.proc.stdin is not None
        assert self.proc.stdout is not None
        assert self.proc.stderr is not None
        self.stdin = self.proc.stdin
        self.stdout = self.proc.stdout
        self.stderr = self.proc.stderr
        self.messages: queue.Queue[dict[str, Any] | BaseException] = queue.Queue()
        self.stderr_path = stderr_path
        self._reader = threading.Thread(target=self._read_loop, daemon=True)
        self._stderr_reader = threading.Thread(target=self._stderr_loop, daemon=True)
        self._reader.start()
        self._stderr_reader.start()
        self._next_id = 1
        self.uri = base.TARGET.resolve().as_uri()
        self.version = 0

    def _answer_server_request(self, item: dict[str, Any]) -> bool:
        if "id" not in item or "method" not in item:
            return False
        method = str(item.get("method"))
        params = item.get("params", {})
        if method == "workspace/configuration":
            result: Any = [None] * len(params.get("items", []))
        elif method == "workspace/workspaceFolders":
            result = [{"uri": self.root.as_uri(), "name": self.root.name}]
        elif method in (
            "client/registerCapability",
            "client/unregisterCapability",
            "window/workDoneProgress/create",
        ):
            result = None
        elif method == "workspace/applyEdit":
            result = {"applied": False, "failureReason": "read-only tournament client"}
        else:
            self.send(
                {
                    "jsonrpc": "2.0",
                    "id": item["id"],
                    "error": {"code": -32601, "message": f"unsupported client method: {method}"},
                }
            )
            return True
        self.send({"jsonrpc": "2.0", "id": item["id"], "result": result})
        return True

    def request(
        self,
        method: str,
        params: dict[str, Any],
        timeout: float = 120.0,
    ) -> dict[str, Any]:
        request_id = self._next_id
        self._next_id += 1
        self.send({"jsonrpc": "2.0", "id": request_id, "method": method, "params": params})
        deadline = time.monotonic() + timeout
        postponed: list[dict[str, Any] | BaseException] = []
        try:
            while time.monotonic() < deadline:
                remaining = max(0.05, deadline - time.monotonic())
                item = self.messages.get(timeout=remaining)
                if isinstance(item, BaseException):
                    raise item
                if self._answer_server_request(item):
                    continue
                if item.get("id") == request_id:
                    return item
                postponed.append(item)
        finally:
            for item in postponed:
                self.messages.put(item)
        raise TimeoutError(f"LSP request timed out: {method}")

    def _wait_diagnostics(self, version: int, timeout: float) -> list[dict[str, Any]]:
        deadline = time.monotonic() + timeout
        latest: list[dict[str, Any]] | None = None
        last_update = 0.0
        saw_busy = False
        saw_idle_after_busy = False
        while time.monotonic() < deadline:
            now = time.monotonic()
            if latest is not None:
                quiet = now - last_update
                if saw_idle_after_busy and quiet >= 0.75:
                    return latest
                if quiet >= 4.0:
                    return latest
            wait_for = min(0.5, max(0.05, deadline - now))
            try:
                item = self.messages.get(timeout=wait_for)
            except queue.Empty:
                continue
            if isinstance(item, BaseException):
                raise item
            if self._answer_server_request(item):
                continue
            method = item.get("method")
            params = item.get("params", {})
            if method == "textDocument/publishDiagnostics":
                if params.get("uri") != self.uri:
                    continue
                published_version = params.get("version")
                if published_version is not None and int(published_version) < version:
                    continue
                latest = list(params.get("diagnostics", []))
                last_update = time.monotonic()
            elif method == "$/lean/fileProgress":
                text_document = params.get("textDocument", {})
                if text_document.get("uri") not in (None, self.uri):
                    continue
                processing = params.get("processing", [])
                if processing:
                    saw_busy = True
                elif saw_busy:
                    saw_idle_after_busy = True
                    last_update = time.monotonic()
        if latest is None:
            raise TimeoutError(f"no Lean diagnostics for version {version}")
        return latest


base.LeanLsp = FixedLeanLsp

if __name__ == "__main__":
    raise SystemExit(base.main())
