#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys

QYM_PATH = "PrimalitySheafVerification/QYM.lean"
DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
)
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"Lean\.ofReduceBool"),
    "global_axiom": re.compile(r"(?m)^\s*axiom\s+"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\s+"),
    "maxHeartbeats_zero": re.compile(r"set_option\s+maxHeartbeats\s+0\b"),
}
EXCLUDED_SCRIPTS = {
    "qym_gb85_v10_orchestrate.py",
    "qym_gb85_v12_select.py",
    "qym_gb85_v15_discover.py",
    "qym_gb85_v15_select.py",
}


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob_bytes(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def audit(text: str) -> dict[str, int]:
    return {name: len(regex.findall(text)) for name, regex in FORBIDDEN.items()}


def declarations(text: str) -> list[re.Match[str]]:
    return list(DECL_RE.finditer(text))


def declaration_at_line(text: str, line: int) -> tuple[str, int, int, str]:
    starts = declarations(text)
    if not starts:
        raise ValueError("no top-level declarations found")
    offset = 0
    if line > 1:
        cursor = 0
        for _ in range(line - 1):
            cursor = text.find("\n", cursor)
            if cursor < 0:
                offset = len(text)
                break
            cursor += 1
        else:
            offset = cursor
    chosen_index = 0
    for index, match in enumerate(starts):
        if match.start() <= offset:
            chosen_index = index
        else:
            break
    chosen = starts[chosen_index]
    end = starts[chosen_index + 1].start() if chosen_index + 1 < len(starts) else len(text)
    return chosen.group("name"), chosen.start(), end, text[chosen.start():end]


def declaration_by_name(text: str, name: str) -> tuple[int, int, str] | None:
    starts = declarations(text)
    for index, match in enumerate(starts):
        if match.group("name") != name:
            continue
        end = starts[index + 1].start() if index + 1 < len(starts) else len(text)
        return match.start(), end, text[match.start():end]
    return None


def patch_constraints(script_text: str, source_raw: bytes) -> str:
    source_sha = sha256_bytes(source_raw)
    source_blob = git_blob_bytes(source_raw)
    result = script_text
    result = re.sub(
        r"(?im)([A-Z0-9_]*(?:BASE|SOURCE|INPUT|EXPECTED)[A-Z0-9_]*SHA256[A-Z0-9_]*\s*(?::[^=\n]+)?=\s*[\"'])([0-9a-f]{64})([\"'])",
        lambda m: m.group(1) + source_sha + m.group(3),
        result,
    )
    result = re.sub(
        r"(?im)([A-Z0-9_]*(?:BASE|SOURCE|INPUT|EXPECTED)[A-Z0-9_]*(?:BLOB|GIT_BLOB)[A-Z0-9_]*\s*(?::[^=\n]+)?=\s*[\"'])([0-9a-f]{40})([\"'])",
        lambda m: m.group(1) + source_blob + m.group(3),
        result,
    )
    known_sha = {
        "830563b33d873354809594d9e9dce962c1253052f8e70bd4d1513226f7598217",
        "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210",
    }
    known_blob = {
        "e796aa6ae9f01965116902a9345ed69f81bcfc42",
        "bd28d0436230a8f0bcb01806dac01787542256b8",
    }
    for old in known_sha:
        result = result.replace(old, source_sha)
    for old in known_blob:
        result = result.replace(old, source_blob)
    return result


def variants_from_script(text: str) -> list[str]:
    result: list[str] = []
    for match in re.finditer(r"(?s)VARIANTS\s*=\s*\{(.*?)\}", text):
        result.extend(re.findall(r"[\"']([A-Za-z0-9_.-]{2,80})[\"']", match.group(1)))
    for match in re.finditer(r"(?s)choices\s*=\s*\[(.*?)\]", text):
        result.extend(re.findall(r"[\"']([A-Za-z0-9_.-]{2,80})[\"']", match.group(1)))
    return list(dict.fromkeys(result))[:30]


def run_patcher(
    repo: Path,
    script: Path,
    source: Path,
    candidate_root: Path,
    source_audit: dict[str, int],
) -> list[tuple[Path, dict]]:
    source_raw = source.read_bytes()
    script_text = patch_constraints(script.read_text(encoding="utf-8"), source_raw)
    patched_script = candidate_root / "patched_patcher.py"
    candidate_root.mkdir(parents=True, exist_ok=True)
    patched_script.write_text(script_text, encoding="utf-8")
    variants = variants_from_script(script_text)
    invocations: list[tuple[str, list[str]]] = [
        ("plain-io", ["{input}", "{output}"]),
        ("flags-io", ["--input", "{input}", "--output", "{output}"]),
    ]
    for variant in variants:
        invocations.extend([
            (variant + "-vio", [variant, "{input}", "{output}"]),
            (variant + "-iov", ["{input}", "{output}", variant]),
            (variant + "-flags", ["--variant", variant, "--input", "{input}", "--output", "{output}"]),
            (variant + "-mixed", [variant, "--input", "{input}", "--output", "{output}"]),
        ])
    generated: list[tuple[Path, dict]] = []
    seen: set[str] = set()
    for index, (label, pattern) in enumerate(invocations[:80]):
        attempt = candidate_root / f"attempt-{index:03d}-{re.sub('[^A-Za-z0-9_.-]+', '-', label)}"
        attempt.mkdir(parents=True, exist_ok=True)
        input_path = attempt / "QYM.input.lean"
        output_path = attempt / "QYM.output.lean"
        shutil.copy2(source, input_path)
        args = [
            str(input_path) if item == "{input}" else str(output_path) if item == "{output}" else item
            for item in pattern
        ]
        try:
            proc = subprocess.run(
                [sys.executable, str(patched_script), *args],
                cwd=repo,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=120,
            )
            log = proc.stdout
            exit_code = proc.returncode
        except subprocess.TimeoutExpired as exc:
            log = (exc.stdout or "") + "\nPATCHER TIMEOUT\n"
            exit_code = 124
        (attempt / "patcher.log").write_text(log, encoding="utf-8")
        possible = []
        if output_path.exists():
            possible.append(output_path)
        if input_path.exists():
            possible.append(input_path)
        possible.extend(sorted(attempt.glob("*.lean")))
        for candidate in possible:
            raw = candidate.read_bytes()
            digest = sha256_bytes(raw)
            if digest == sha256_bytes(source_raw) or digest in seen:
                continue
            try:
                candidate_text = raw.decode("utf-8")
            except UnicodeDecodeError:
                continue
            if audit(candidate_text) != source_audit:
                continue
            if len(raw) < int(len(source_raw) * 0.75) or len(raw) > int(len(source_raw) * 1.25):
                continue
            seen.add(digest)
            final = attempt / f"candidate-{len(generated):02d}.lean"
            if candidate != final:
                shutil.copy2(candidate, final)
            generated.append((final, {
                "method": "patcher",
                "script": str(script.relative_to(repo)),
                "invocation": args,
                "invocation_label": label,
                "patcher_exit": exit_code,
                "candidate_sha256": digest,
                "candidate_blob": git_blob_bytes(raw),
            }))
    return generated


def historical_refs(repo: Path) -> list[str]:
    proc = subprocess.run(
        ["git", "for-each-ref", "--sort=-committerdate", "--format=%(refname)", "refs/heads", "refs/remotes/origin"],
        cwd=repo,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=True,
    )
    return [line.strip() for line in proc.stdout.splitlines() if line.strip() and not line.endswith("/HEAD")]


def git_show(repo: Path, ref: str) -> bytes | None:
    proc = subprocess.run(
        ["git", "show", f"{ref}:{QYM_PATH}"],
        cwd=repo,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    return proc.stdout if proc.returncode == 0 else None


def main() -> None:
    if len(sys.argv) != 6:
        raise SystemExit("usage: discover.py REPO SOURCE FRONTIER_JSON OUT LIMIT")
    repo = Path(sys.argv[1]).resolve()
    source = Path(sys.argv[2]).resolve()
    frontier_path = Path(sys.argv[3]).resolve()
    out = Path(sys.argv[4]).resolve()
    limit = int(sys.argv[5])
    out.mkdir(parents=True, exist_ok=True)
    candidate_dir = out / "candidates"
    candidate_dir.mkdir(parents=True, exist_ok=True)

    source_raw = source.read_bytes()
    source_text = source_raw.decode("utf-8")
    source_sha = sha256_bytes(source_raw)
    source_audit = audit(source_text)
    frontier = json.loads(frontier_path.read_text(encoding="utf-8"))
    first = frontier.get("first_error") or {}
    first_line = int(first.get("line") or 1)
    decl_name, decl_start, decl_end, decl_text = declaration_at_line(source_text, first_line)
    lines = source_text.splitlines()
    context_start = max(0, first_line - 80)
    context_end = min(len(lines), first_line + 160)
    context = "\n".join(lines[context_start:context_end])
    tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_'.]{5,}", str(first.get("message") or "") + "\n" + context)
    anchors = [decl_name] + [token for token in tokens if token not in {"theorem", "ContDiff", "Mathlib"}]
    anchors = list(dict.fromkeys(anchors))[:80]

    discovery: dict = {
        "schema": "qym-gb85-v15-discovery",
        "source_sha256": source_sha,
        "source_blob": git_blob_bytes(source_raw),
        "frontier": frontier,
        "target_declaration": decl_name,
        "target_declaration_start_line": source_text.count("\n", 0, decl_start) + 1,
        "anchors": anchors,
        "scripts": [],
        "historical_refs_examined": 0,
        "candidates": [],
    }

    pool: list[tuple[bytes, dict]] = []
    scripts: list[tuple[int, Path]] = []
    for script in (repo / ".github").rglob("*.py"):
        if script.name in EXCLUDED_SCRIPTS:
            continue
        try:
            script_text = script.read_text(encoding="utf-8")
        except Exception:
            continue
        score = sum(8 if anchor == decl_name and anchor in script_text else 1 for anchor in anchors if anchor in script_text)
        if score > 0:
            scripts.append((score, script))
    scripts.sort(key=lambda item: (-item[0], str(item[1])))

    for score, script in scripts[:24]:
        script_root = out / "patcher-attempts" / re.sub(r"[^A-Za-z0-9_.-]+", "-", str(script.relative_to(repo)))
        generated = run_patcher(repo, script, source, script_root, source_audit)
        discovery["scripts"].append({
            "path": str(script.relative_to(repo)),
            "score": score,
            "generated": len(generated),
        })
        for candidate_path, metadata in generated:
            pool.append((candidate_path.read_bytes(), metadata))

    seen_blobs: set[str] = set()
    historical_blocks: set[str] = set()
    whole_sources_added = 0
    for ref in historical_refs(repo)[:300]:
        raw = git_show(repo, ref)
        if raw is None:
            continue
        blob = git_blob_bytes(raw)
        if blob in seen_blobs:
            continue
        seen_blobs.add(blob)
        discovery["historical_refs_examined"] += 1
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError:
            continue
        found = declaration_by_name(text, decl_name)
        if found is None:
            continue
        _, _, historical_decl = found
        block_sha = sha256_bytes(historical_decl.encode("utf-8"))
        if historical_decl != decl_text and block_sha not in historical_blocks:
            historical_blocks.add(block_sha)
            candidate_text = source_text[:decl_start] + historical_decl.rstrip() + "\n\n" + source_text[decl_end:]
            if audit(candidate_text) == source_audit:
                pool.append((candidate_text.encode("utf-8"), {
                    "method": "historical-declaration",
                    "ref": ref,
                    "declaration": decl_name,
                    "historical_block_sha256": block_sha,
                }))
        if (
            whole_sources_added < 4
            and raw != source_raw
            and audit(text) == source_audit
            and int(len(source_raw) * 0.80) <= len(raw) <= int(len(source_raw) * 1.20)
        ):
            pool.append((raw, {"method": "historical-whole-source", "ref": ref, "blob": blob}))
            whole_sources_added += 1

    unique: set[str] = {source_sha}
    selected: list[str] = []
    for raw, metadata in pool:
        digest = sha256_bytes(raw)
        if digest in unique:
            continue
        unique.add(digest)
        name = f"candidate-{len(selected):03d}"
        target = candidate_dir / name
        target.mkdir(parents=True, exist_ok=True)
        (target / "QYM.lean").write_bytes(raw)
        metadata = {
            **metadata,
            "name": name,
            "candidate_sha256": digest,
            "candidate_blob": git_blob_bytes(raw),
            "bytes": len(raw),
            "lf": raw.count(b"\n"),
            "forbidden": source_audit,
        }
        (target / "metadata.json").write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        selected.append(name)
        discovery["candidates"].append(metadata)
        if len(selected) >= limit:
            break

    matrix = selected if selected else ["__none__"]
    (out / "matrix.json").write_text(json.dumps({"candidate": matrix}, separators=(",", ":")) + "\n", encoding="utf-8")
    (out / "DISCOVERY.json").write_text(json.dumps(discovery, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out / "TARGET_CONTEXT.txt").write_text(context + "\n", encoding="utf-8")
    print(json.dumps(discovery, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
