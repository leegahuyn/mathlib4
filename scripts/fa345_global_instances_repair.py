from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
import json
from pathlib import Path
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "59d4bcc02ff615190da0691c9bef52fe3d8bfcb0b8cdf573c300e258757376b6"
EXPECTED_OUTPUT_SHA256 = "a847847aa1ed548a69e3b76e061f4ebfebfeb99cb0538ca491f83ca867d42479"
PAYLOAD = """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"""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass345-global] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass345-global input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    replacements = json.loads(decompress(b64decode(PAYLOAD)).decode("utf-8"))
    for item in replacements:
        old = item["old"]
        new = item["new"]
        expected = int(item["expected"])
        count = text.count(old)
        print(f'{item["name"]}: expected={expected} actual={count}')
        if count != expected:
            raise RuntimeError(
                f'{item["name"]}: expected {expected} occurrence(s), found {count}'
            )
        text = text.replace(old, new)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass345-global output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass345-global] coherent fixed-phase instances installed at alias")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
