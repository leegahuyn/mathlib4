from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
import json
from pathlib import Path
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "c980501c4a7f0f6582c5d67ec7fa08c7af37ffd6aa3335a3724928f94c2de03f"
EXPECTED_OUTPUT_SHA256 = "2c4376b7b6adaabe7917bbfbc327c622da252a585835461881a9e3ac336dc607"
PAYLOAD = """eNq1Vs1S5DYQfpUuLhkvjtc/M54xVRxSBFiqyGYD3Ajr0tgaRllbcmR7YTilUnvZQx4hl1TyBHmPPARPkm75B88wbDgQDo2wWl9/3a2vxeWlN57MJnZjL3ekkonKi7pi84yDkGXFZMJhVGihtKhWsLcPvuu61o9yx94B/BHyI9clP6zYkbjl6bslK/mB0vybND1Qef6dkkqkMJKwB/ef/rRgrz+54XHyBBBIPLTfnhr9R7hjreoCTziVWoM3x9FcXdkm44gyjlzMmJgkSyavMUvPkPzVgvtf/oBbx4N9sj1hfsuSCpTkcZnXGXm22y1q5BvUYAOVwSuYDzGZWc+7Lxv4CN3gM3RZxzd9isJ1/AZt5CL381ypavlDrSrBZYXZFwh4VMukEgqruA/uRiyKE99xrYANwsxMmGhrGMpgF1aOZ/WJNJ+a9epROiYES1N0IMfVIKHQ9Wyy/qOC7W4rWBPnqbJhiO1lC92xiTLZiOI+bvZmeagyW3sdTd3ARuu5jzST8gUkSulUSFbxcuvN7zr0RmRzrrFRvXvvAl8UxNDtez0X1TteoW+pZAv5LB+ktgue9TzPr8kTbpZc89Z/jnxoHmT+QwIg203NRMlT2m5WW1wydYNgxqddbjhRqX03nIQ22WnbPyR5zPKcXdyoro7HXOW80ivnut24UOen/hlnrZL++RvuLKdc5XmH6k2CwCY7NqilQKmgsrMVXCbKTL1OPgd1WVwwkcUVGf6zkYsNUuncLK86SD+Yjm2yk5ckGnhjJIp23KIS1ZZpzgpzzIYzIa/fqNwRacyKIltdbVzkkVFhWc8hgRjizRBUYbTT/y/ELPRsssFWvSxXBddzlYnkWy5LemZGd0Y1v1nm1+/3n/9yB4+AB6/h7Vsqm5N/gDtH5MbEhSqdjFvwHvw+chRiV9CGfVcepv1rc8z4w6uBCujHoL6H0WhUMGRndHF4W+D0l6iuXtPEzkIgH+fhGsJLww/O60X2kF5EhY3aR2fQubODU/GBO0JKrpuOfWUDXmxNjTyUbRdtoA5Tg3t8uvcZv3VQBz/FakFVtrtqmx5jx+xmrKMa2qMdmZkhE/W11his2x67OO/J4rxvP3gBffAaxXR9MZTNxB0pU5Y6yUTKmTxmNe5LqFEkw5n1tJfl4Ljch7j1Hsq8S7PJMNbchrrA+ghdnhCB9ibGJc8W9kMKgWEcDNXYIT7j+CSM8Phk6j5WGu/4n9G8NEk0/aLHs10Ni40onsHqXs+1UtOjRzb8QqBTGrpHWuXndZJsD4hytgeV7kk0K8mv7fXrcmJvvT4DWlNDa7aVcxDSZtCMIX0Dl0JW/Fpjd1g+p/F5wcuKXkAzkroBVNTlMk5YWXUvzxpmSP0Kw/ELYk594jn1Zw9zvpUH/mcoFgsHS23GEf5JL4RlTl79C5WdlUk="""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass348] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected PASS 348 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    lines = text.splitlines(keepends=True)
    operations = json.loads(decompress(b64decode(PAYLOAD)).decode("utf-8"))
    print(f"line_operations={len(operations)}")
    for start, stop, replacement in reversed(operations):
        lines[start:stop] = replacement
    output = "".join(lines)
    output_sha = digest(output)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected PASS 348 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(output, encoding="utf-8")
    print("[pass348] coherent fixed-core and independent FA frontiers repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
