from __future__ import annotations

import hashlib
import json
import os
import queue
import re
import subprocess
import threading
import time
from dataclasses import asdict
from pathlib import Path
from typing import Any, Iterable

import fa417_history_mining_tournament as history

core = history.core
ROOT = core.ROOT
TARGET = core.TARGET
OUT = ROOT / "build-logs" / "fa418-lsp-strict"
OUT.mkdir(parents=True, exist_ok=True)

INITIAL_SHA = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
FLOOR_LINE = 31725
MAX_FRONTIERS = int(os.environ.get("FA418_MAX_FRONTIERS", "48"))
MAX_CANDIDATES = int(os.environ.get("FA418_MAX_CANDIDATES", "100"))


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def error_line(diagnostic: dict[str, Any]) -> int:
    return int(diagnostic.get("range", {}).get("start", {}).get("line", 0)) + 1


def error_col(diagnostic: dict[str, Any]) -> int:
    return int(diagnostic.get("range", {}).get("start", {}).get("character", 0)) + 1


def first_lsp_error(diagnostics: list[dict[str, Any]]) -> dict[str, Any] | None:
    errors = [d for d in diagnostics if int(d.get("severity", 1)) == 1]
    if not errors:
        return None
    return min(errors, key=lambda d: (error_line(d), error_col(d)))


class LeanLsp:
    def __init__(self, root: Path, stderr_path: Path) -> None:
        self.root = root.resolve()
        self.proc = subprocess.Popen(
            [
                "lake",
                "env",
                "lean",
                "--server",
                "-DwarningAsError=false",
                "-DmaxErrors=200",
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
        self.uri = TARGET.resolve().as_uri()
        self.version = 0

    def _stderr_loop(self) -> None:
        with self.stderr_path.open("wb") as f:
            while True:
                chunk = self.stderr.read(65536)
                if not chunk:
                    break
                f.write(chunk)
                f.flush()

    def _read_exact(self, n: int) -> bytes:
        chunks: list[bytes] = []
        remaining = n
        while remaining:
            chunk = self.stdout.read(remaining)
            if not chunk:
                raise EOFError("Lean LSP stdout closed")
            chunks.append(chunk)
            remaining -= len(chunk)
        return b"".join(chunks)

    def _read_loop(self) -> None:
        try:
            while True:
                headers: dict[str, str] = {}
                while True:
                    line = self.stdout.readline()
                    if not line:
                        raise EOFError("Lean LSP stdout closed")
                    if line in (b"\r\n", b"\n"):
                        break
                    decoded = line.decode("ascii", errors="replace").strip()
                    if ":" in decoded:
                        key, value = decoded.split(":", 1)
                        headers[key.lower().strip()] = value.strip()
                length = int(headers["content-length"])
                payload = self._read_exact(length)
                self.messages.put(json.loads(payload.decode("utf-8")))
        except BaseException as exc:
            self.messages.put(exc)

    def send(self, message: dict[str, Any]) -> None:
        payload = json.dumps(message, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        packet = f"Content-Length: {len(payload)}\r\n\r\n".encode("ascii") + payload
        self.stdin.write(packet)
        self.stdin.flush()

    def request(self, method: str, params: dict[str, Any], timeout: float = 120.0) -> dict[str, Any]:
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
                if item.get("id") == request_id:
                    return item
                postponed.append(item)
        finally:
            for item in postponed:
                self.messages.put(item)
        raise TimeoutError(f"LSP request timed out: {method}")

    def initialize(self) -> None:
        response = self.request(
            "initialize",
            {
                "processId": os.getpid(),
                "rootUri": self.root.as_uri(),
                "workspaceFolders": [{"uri": self.root.as_uri(), "name": self.root.name}],
                "capabilities": {
                    "workspace": {"configuration": True},
                    "textDocument": {
                        "publishDiagnostics": {"relatedInformation": True, "versionSupport": True},
                        "synchronization": {"didSave": False, "willSave": False},
                    },
                },
                "clientInfo": {"name": "fa418-strict-tournament", "version": "1"},
            },
            timeout=180.0,
        )
        if "error" in response:
            raise RuntimeError(f"Lean LSP initialize failed: {response['error']}")
        self.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})

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

    def open(self, text: str, timeout: float = 1200.0) -> list[dict[str, Any]]:
        self.version = 1
        self.send(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": self.uri,
                        "languageId": "lean4",
                        "version": self.version,
                        "text": text,
                    }
                },
            }
        )
        return self._wait_diagnostics(self.version, timeout)

    def change(self, text: str, timeout: float = 300.0) -> list[dict[str, Any]]:
        self.version += 1
        self.send(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didChange",
                "params": {
                    "textDocument": {"uri": self.uri, "version": self.version},
                    "contentChanges": [{"text": text}],
                },
            }
        )
        return self._wait_diagnostics(self.version, timeout)

    def close(self) -> None:
        try:
            self.send(
                {
                    "jsonrpc": "2.0",
                    "method": "textDocument/didClose",
                    "params": {"textDocument": {"uri": self.uri}},
                }
            )
            self.request("shutdown", {}, timeout=10.0)
            self.send({"jsonrpc": "2.0", "method": "exit", "params": {}})
        except Exception:
            pass
        try:
            self.proc.terminate()
            self.proc.wait(timeout=10)
        except Exception:
            self.proc.kill()


def cli_probe(label: str, max_errors: int = 1):
    # fa417 patched compile_fa to use a one-error tournament probe except for
    # authoritative labels.  Use a non-authoritative label here intentionally.
    return core.compile_fa(label, max_errors=max_errors)


def strict_better(candidate: Any, champion: Any) -> bool:
    if candidate.passed:
        return True
    return (
        candidate.first_line is not None
        and champion.first_line is not None
        and candidate.first_line > champion.first_line
    )


def collect_candidates(
    source: str,
    declaration: Any,
    branches: list[str],
    limit: int,
) -> list[tuple[str, str]]:
    expected_imports = core.imports(source)
    candidates: list[tuple[str, str]] = []
    seen = {sha256_text(source)}

    for label, donor in core.donor_sources(branches):
        if len(candidates) >= limit:
            break
        if not core.valid_donor(donor, expected_imports):
            continue
        donor_decl = core.matching_declaration(donor, declaration)
        if donor_decl is None:
            continue
        candidate = core.replace_declaration_same_height(source, declaration, donor, donor_decl)
        if candidate is None:
            continue
        digest = sha256_text(candidate)
        if digest in seen:
            continue
        seen.add(digest)
        candidates.append((label, candidate))

    for label, candidate in core.generic_candidates(source, declaration):
        if len(candidates) >= limit:
            break
        digest = sha256_text(candidate)
        if digest in seen:
            continue
        if core.imports(candidate) != expected_imports or any(core.forbidden_hits(candidate).values()):
            continue
        seen.add(digest)
        candidates.append((f"generic:{label}", candidate))
    return candidates


def diag_summary(diagnostics: list[dict[str, Any]]) -> dict[str, Any]:
    first = first_lsp_error(diagnostics)
    return {
        "diagnostic_count": len(diagnostics),
        "error_count": sum(int(d.get("severity", 1)) == 1 for d in diagnostics),
        "first_line": error_line(first) if first else None,
        "first_col": error_col(first) if first else None,
        "first_message": str(first.get("message", "")) if first else "",
    }


def main() -> int:
    source = TARGET.read_text(encoding="utf-8")
    initial_sha = sha256_text(source)
    previous_status = OUT / "CURRENT.json"
    if initial_sha != INITIAL_SHA and not previous_status.exists():
        # A parent branch may already contain a strictly checked-in champion.  Require
        # an authoritative compile at or beyond the immutable floor before accepting it.
        floor_probe = cli_probe("parent-champion-floor-probe", 1)
        if not floor_probe.passed and (
            floor_probe.first_line is None or floor_probe.first_line < FLOOR_LINE
        ):
            raise SystemExit(
                f"untrusted inherited source {initial_sha}, first error {floor_probe.first_line}"
            )
    if any(core.forbidden_hits(source).values()):
        raise SystemExit(f"forbidden executable token in starting source: {core.forbidden_hits(source)}")

    prerequisites = core.verify_prerequisites()
    branches = core.remote_branches()
    champion = cli_probe("baseline-cli-first-error", 1)
    if not champion.passed and (
        champion.first_line is None or champion.first_line < FLOOR_LINE
    ):
        raise SystemExit(f"baseline below immutable floor: {champion}")

    lsp = LeanLsp(ROOT, OUT / "lean-lsp.stderr.log")
    history_rows: list[dict[str, Any]] = []
    any_promotion = False
    try:
        lsp.initialize()
        diagnostics = lsp.open(source)
        lsp_first = first_lsp_error(diagnostics)
        if not champion.passed and lsp_first is not None:
            lsp_line = error_line(lsp_first)
            # LSP is only a screening tool, but a grossly earlier diagnostic means the
            # incremental session is not equivalent enough to use safely.
            if lsp_line < FLOOR_LINE:
                raise RuntimeError(
                    f"LSP session regressed below immutable floor: {lsp_line}"
                )

        for frontier in range(1, MAX_FRONTIERS + 1):
            if champion.passed:
                break
            assert champion.first_line is not None
            declaration = core.declaration_at(source, champion.first_line)
            if declaration is None:
                history_rows.append(
                    {
                        "frontier": frontier,
                        "reason": "no enclosing declaration",
                        "champion": asdict(champion),
                    }
                )
                break

            candidates = collect_candidates(
                source, declaration, branches, MAX_CANDIDATES
            )
            tested: list[dict[str, Any]] = []
            promoted = False
            for index, (label, candidate) in enumerate(candidates, 1):
                candidate_diags = lsp.change(candidate)
                summary = diag_summary(candidate_diags)
                lsp_line = summary["first_line"]
                lsp_better = lsp_line is None or lsp_line > champion.first_line
                row: dict[str, Any] = {
                    "index": index,
                    "label": label,
                    "source_sha256": sha256_text(candidate),
                    "lsp": summary,
                    "lsp_strictly_better": lsp_better,
                }
                if not lsp_better:
                    tested.append(row)
                    diagnostics = lsp.change(source)
                    continue

                TARGET.write_text(candidate, encoding="utf-8")
                actual = cli_probe(
                    f"frontier-{frontier:02d}-candidate-{index:03d}-cli", 1
                )
                row["cli"] = asdict(actual)
                row["cli_strictly_better"] = strict_better(actual, champion)
                tested.append(row)
                if strict_better(actual, champion):
                    source = candidate
                    champion = actual
                    diagnostics = candidate_diags
                    promoted = True
                    any_promotion = True
                    (OUT / f"frontier-{frontier:02d}-PROMOTED.txt").write_text(
                        f"label={label}\n"
                        f"source_sha256={actual.source_sha256}\n"
                        f"exit_code={actual.exit_code}\n"
                        f"first_error={actual.first_line}:{actual.first_col}\n",
                        encoding="utf-8",
                    )
                    break

                TARGET.write_text(source, encoding="utf-8")
                diagnostics = lsp.change(source)

            history_rows.append(
                {
                    "frontier": frontier,
                    "declaration": asdict(declaration),
                    "candidate_count": len(candidates),
                    "promoted": promoted,
                    "champion_after": asdict(champion),
                    "tested": tested,
                }
            )
            if not promoted:
                break
    finally:
        lsp.close()

    TARGET.write_text(source, encoding="utf-8")
    # Full diagnostic replay is authoritative; it may not rely on LSP or maxErrors=1.
    authoritative = history._original_compile_fa(
        "final-fa-authoritative", max_errors=500
    )
    if not authoritative.passed and (
        authoritative.first_line is None or authoritative.first_line < FLOOR_LINE
    ):
        raise SystemExit(f"authoritative replay below immutable floor: {authoritative}")

    complete = False
    two_pass: dict[str, list[dict[str, Any]]] = {}
    downstream_failure: str | None = None
    if authoritative.passed:
        try:
            two_pass = core.verify_all_twice()
            complete = True
        except Exception as exc:
            downstream_failure = repr(exc)

    lines = source.splitlines()
    line = authoritative.first_line or 1
    start = max(1, line - 55)
    end = min(len(lines), line + 85)
    (OUT / "FIRST_ERROR_CONTEXT.txt").write_text(
        "\n".join(f"{i}: {lines[i - 1]}" for i in range(start, end + 1)),
        encoding="utf-8",
    )
    status = {
        "complete": complete,
        "stage": "ALL_REQUIRED_TARGETS_2X_PASS" if complete else "Mock2_FunctionalAnalysis",
        "immutable_floor": {"sha256": INITIAL_SHA, "first_error_line": FLOOR_LINE},
        "screening_policy": "LSP screens candidates; only direct CLI Lean compile may promote",
        "promotion_policy": "exit 0 or direct CLI first_error strictly later; never error-count-only",
        "starting_sha256": initial_sha,
        "any_promotion": any_promotion,
        "prerequisites": prerequisites,
        "final_fa_metric": asdict(authoritative),
        "frontiers": history_rows,
        "forbidden_token_audit": core.forbidden_hits(source),
        "two_pass": two_pass,
        "downstream_failure": downstream_failure,
    }
    (OUT / "CURRENT.json").write_text(json.dumps(status, indent=2), encoding="utf-8")
    (OUT / "CURRENT.txt").write_text(
        f"complete={complete}\n"
        f"stage={status['stage']}\n"
        f"any_promotion={any_promotion}\n"
        f"fa_exit={authoritative.exit_code}\n"
        f"fa_errors={authoritative.errors}\n"
        f"fa_first={authoritative.first_line}:{authoritative.first_col}\n"
        f"fa_sha256={authoritative.source_sha256}\n"
        f"downstream_failure={downstream_failure}\n",
        encoding="utf-8",
    )
    print(json.dumps(status, indent=2))
    return 0 if complete else 2


if __name__ == "__main__":
    raise SystemExit(main())
