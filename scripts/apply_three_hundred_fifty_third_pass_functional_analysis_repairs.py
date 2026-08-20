from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
import json
from pathlib import Path
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "0086014f12003ed303f8c5858e506df5c69c28985b660c4ebe573110873f65a0"
EXPECTED_OUTPUT_SHA256 = "986d7a309dc10a15e6bc918b17484d5873ab1364c2e72a7228a9be939925bd30"
PAYLOAD = """eNrtWMtu20YU/ZULrciUJiT5IdtAgAKqlRh17MQq0IWjEBQ5JKclZ+ghaUkuCiRBkV2Boot21a/pn/hLeocP8SHKtpT0EaBaWJR8X+fcMzN3dPVDh/Y6x/3efrevdbhvd447kL4sz2Qugbu3vyldOIYhZzFlCU+iMYmuE+pTRkwx4iKA5yoawVPovmaZK5mbVgwKw38at0RwdN8kjPqadbQOI7NlLWYY+gtI45HrNKQehKJIJxwfPX7Ucii7vb29AkotjnLKboiIyElsjuic2C89MyJDLoge828Jdb14TKyYcoalwxfQU4sEynpPYdKIAFuapuZWEoXDJOaOcxESYcZcwDkwSFTYKe3arfLM9XgPZcfIqgq3yJ0h/cQMrgIzNKJkOpGfs07WKdrvlt32zBsCHpYCxzXmZZzI47OG515dJxlBCfZ2HHAee68SHlPC4iEPQpTBKGEpp6oUwU8/w92HX/H9PX58CtNFBjNtYJZPlqFBiuvSnBlB4htWyhEoSRjFJhXRcMmbIYjpZ1nhPKfsEZXoPb0/WdHYtjgcwQOJQMuxbF/6RsVXOjLof7zcdx4nd5/PiPi0ct95vNzz7FvIfXC4rdwP+3+/3FNcn6fcP6L0LeV+dHhQdiSiQQic4eFwdTk8o98TnTJGhJEeGBrIaD6Z6xZn3xncucQiNDg/l+96JCu2iZNpxvStrCoDZaUoyq1OA3gDJLF8ahOTPTMTl5zMQ86wSJSgZOWPjBwk5Q30VXhSEXsGKgeTLbZ85RVr7kY+51aCoJqfVNcA8iceEyVpRFFrQkONUebWcCneAlfflPvU+oqwiMYLTF0HUytEUWZp3hGdEjFGmggoO6GJMS7ElMYlI2ozjvofZUSuuhTIpCTGaGOtsmC2kZks+BIDnTA7t8vCN+SHhvIJxxp8K0NlUeR3k2KvuPvwC1Qqz4tcLoy97u6gulVJl0Y0QZr7QD6prdiBoerRIghqCfYPjpoJ7LkhQYPnwK0G9qL8lLObMnf13PSdoltp64acC5syMybPBCEMd3bERW/JGXHiGlsAD/qKkM9eIIVbuKVsapCEqOcz6sRag55K3/85CJsxtw5GpW2D/foRttzULuWsku5sGkh1rUoW5MFq2nb2IBW6cpC0RluviyUpGyQssRx0d/+X4OcnwYPu0RoJnsn5YYQzxTixrHulWCCpCQRnvlIp6QMjbmNDPl26tu7TXgattg9P1qu8reBPpPZ2MK3Fn2qbgam0Yq/fOj59Q6Ll1JUdTnmJa2mpOL+k97lUk1cujyunrPzCYE7dY/BvljvYsNz93lGveV2Qe9Q4mQbcTnyiByQwuIg97nJm+m1jubT/cp2DnKxAOYE/f4eRimOLkV2BiperV0yV+d37txrg33fqpFHlYPVSI2e0dVmVr+WA5KqghBpcq6qOVHrhNSimBlMVb1TT1vsFhtwECbiV+FVY8rWSroTT7x6uwtmU9s2Jl+Xu4NK1Guz2e22/kDzEbaVzaq11q2R48yIxeBfo1X6321ZD96go6/tq9ir2WivkbO3iQB5yn7sUj4ihz6MEx8sG4kp1ciFamVUD1z3BivormB8KXmOhxF901pCwJn8B3yzygg=="""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass353] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass353 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    lines = text.splitlines(keepends=True)
    hunks = json.loads(decompress(b64decode(PAYLOAD)).decode("utf-8"))
    for reverse_index, hunk in enumerate(reversed(hunks), 1):
        i1 = int(hunk["i1"])
        old = hunk["old"]
        new = hunk["new"]
        old_lines = old.splitlines(keepends=True)
        actual = "".join(lines[i1:i1 + len(old_lines)])
        if actual != old:
            original_index = len(hunks) - reverse_index + 1
            raise RuntimeError(
                f"pass353 hunk {original_index} mismatch at original line {i1 + 1}"
            )
        lines[i1:i1 + len(old_lines)] = new.splitlines(keepends=True)
        print(f"pass353 hunk {len(hunks) - reverse_index + 1}: original_line={i1 + 1}")

    output = "".join(lines)
    output_sha = digest(output)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass353 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(output, encoding="utf-8")
    print("[pass353] FunctionalAnalysis prefix and double-adjoint repairs applied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
