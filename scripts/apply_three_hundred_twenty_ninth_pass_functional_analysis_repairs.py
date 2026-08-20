from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "f39bad641a544d23c59871b91d3e3eb677cf8fca25e0bf49c10d28d48503b576"
EXPECTED_OUTPUT_SHA256 = "d38f2f58649a4acda650c92d4a36a6df063b86dbe144ce958dc1c1a096168189"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(
    text: str, old: str, new: str, label: str, expected: int
) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(
            f"{label}: expected {expected} occurrence(s), found {count}"
        )
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass329] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass329 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    # Mathlib now exposes these through the generic Is*Apply API.  The old
    # TestFunction-qualified theorem names no longer exist; only the name used
    # by `simp only` changes here, not any definition or theorem statement.
    text = replace_exact(
        text,
        "TestFunction.add_apply",
        "add_apply",
        "FunctionalAnalysis current TestFunction addition apply API",
        27,
    )
    text = replace_exact(
        text,
        "TestFunction.sub_apply",
        "sub_apply",
        "FunctionalAnalysis current TestFunction subtraction apply API",
        15,
    )
    text = replace_exact(
        text,
        "TestFunction.smul_apply",
        "smul_apply",
        "FunctionalAnalysis current TestFunction scalar apply API",
        26,
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass329 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass329] FunctionalAnalysis TestFunction apply API migrated")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
