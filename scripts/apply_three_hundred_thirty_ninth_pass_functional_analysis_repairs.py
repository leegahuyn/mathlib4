from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
import json
from pathlib import Path
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "1d150bcb8bd909e1bde7ce3577cf754386efcd7be2902d68a7c78b72b28d6b39"
EXPECTED_OUTPUT_SHA256 = "57f084029aff8e8a4b95d13e0daa9890eaa036716da48b3a3352ac3023be1c25"
PAYLOAD = """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"""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass339] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass339 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    replacements = json.loads(decompress(b64decode(PAYLOAD)).decode("utf-8"))
    for item in replacements:
        old = item["old"]
        new = item["new"]
        count = text.count(old)
        print(f'{item["name"]}: expected=1 actual={count}')
        if count != 1:
            raise RuntimeError(
                f'{item["name"]}: expected one occurrence, found {count}'
            )
        text = text.replace(old, new)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass339 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print(
        "[pass339] graph instances, covariance, cutoff, density, "
        "and Euclidean-gauge frontiers repaired"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
