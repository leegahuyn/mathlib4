from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
import json
from pathlib import Path
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "8831fff80c528bccdd9f7f4a57e1f61703aab00e680bcad6f34feeddaab24039"
EXPECTED_OUTPUT_SHA256 = "0086014f12003ed303f8c5858e506df5c69c28985b660c4ebe573110873f65a0"
PAYLOAD = """eNrtWMtu20YU/ZULrciAYSXHrxh1gcKRGwOpndopuogTYkSNRDbkDD0kLVlJgDQogmRRoOiiuzbdFGiB/kDRXT5FX9I7D75kKZWSIH2gXtgUNXPvuec+5ozvPmyFndbOWmejfc1p8ajf2mmB+qFj4mfAuIi9CRX8lLWcFqOjme+tcgHswPTJ91Yb/+5xloUs53l6QtOzPIxCRonYx5Vw08ZFsAttGw0+doz3a5310nvNjR8QNqSnTLoTJEzpMRmBlZCEiiPRC7PuOOGMMkRp60Xyx7IsP0+TvTzjg8ERLiUZF3AIDHKEdsDOqUhpNyP74Zj2bwckpXtcUDQBO5URgJOY8yz4LOdZiB72eJxguPs587OQy7Uw/fobmD77Dv8+tWECV4vNeZJmJBTpXgkCnU/gSmV86VBkMBL0qlh2wZthd72ZW2shSfYqLK2Ga/dSCf0tqdqdoWarSY3BtTLt+HkXeheXYnzTLBbWalA31/+iRyI+ouK/0SNLh/LOemRz4/8eWdAjm9v/lh7ZvrZZQbUOD48pidz4AUzcMFa/vISnbkTt6Vd/vPod7sNaA4xlddCH3mbDB/AaA2ZvzfV6rYACck4h6J6hteACk9bjUejfoCwNswvJro55kDOsRB3U7kdgTV/+Il2U2BxIzzzGGaND8KYvf61hM6EbK3ScwUR/wkf9kIZxAncveXcAe8jrh+f35DIxwiXdM/WsDnS917I+T3DfTRINbkeEUdcvT3QvjN2QnU+fPgFL40fkihg0K3WAbbsJH8Ga7aZ5L0P3XvygCLjaUQVmlSHbdiMZmsMjRhuKQtvwaqzVUqZ4qWHFx1SFpG0dxHNM1RLwunTvmKy9lpgqYjldSo0kg3CRckmaBGH8BoqJIo0kSaKLBpP6vYbuc2piG4qPxVCbGJeRKyLGKpIfkIVgUtUAgTwN2VCZKHLTKNzrW7XClQUxffYtBCc+iaiuEdzdSAx+42v7Ho5RHASKrftAcz8K+5SwT0g+pNW0NrDUn6eqcez6qLd005tm/4KGwyCTM8zN+AlVjQ/n8tmswuHWOCkwyoyIZazkM1bsRhsVgdbisi737mQmmCvNk2ik/O6HPSoUgWBdnXt+zdqx/6GMyPFQVYImxpvHWlVP6+1OQ22qOcQZ1vbd4tg/wMYXhlEvpdHAKRXBIV4STs6KWVX4kDFEdOzygSx2T0g4jTPkLZyYyGSoc91UgW1UWrHhXG7tj+Ww+RKCAUwc6F9Un2ZsbKw1z9LFG52qoY7ljUF1VUmJbFKZ5mOkv8v6nhofDsQk8Ui/rx/iPHJK7qRd7+ASpeq1DtiBQBcJnju41aNn0kLBz+wUUIfNHIBLI5uL5MB5I2QeGzRp3u68faq2N98gVbekcN0XPD7JfX/1lOEJUsudfMAz8p1StTiJc6AvwFzgWQL6u6y/2SxvdrbnZJlEkTfkJEohExfmCA4G0kptStyhaakrXeXNZGPWc5KngecTKSPqniux9549b7Ub03XxETV98XN7+vxHG6YvfoK20S9dI3FQCxQqw40TAR8+AhQGxStYwxeadpR65VtcVI19HZ0xhyvCwUBZagqYRqmtgNU40ppoAWi5QN9+5Vm9knA3jioXteAr3YaKrYxdiuY5PIQswxeF3HofEq5ZDOvtqhgMF7kUqN2ipz+lJM2F+f+A5Qc8pSjP4pjcGXGswj6JUZCQ6AaPSchcnwgRUgGnp0Wah2Yt3jzZnv7Wlv++m6PUU5pVd86Hhax+BK9+syYwff4clvWO97tKzOit82A8ri5SAKtHtiC6uripXatkGsoLE0baPCq2rl+/LKHlBNSwymwYHyYp96r6m7lVxGoB6UW0G/dovy9nH+Ye38e3cL7KGatNFG3XSMfSAJy5V5qVnCse7v0JIo5vDg=="""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass352] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass352 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
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
                f"pass352 hunk {original_index} mismatch at original line {i1 + 1}"
            )
        lines[i1:i1 + len(old_lines)] = new.splitlines(keepends=True)
        print(f"pass352 hunk {len(hunks) - reverse_index + 1}: original_line={i1 + 1}")

    output = "".join(lines)
    output_sha = digest(output)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass352 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(output, encoding="utf-8")
    print("[pass352] FunctionalAnalysis prefix frontier repairs applied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
