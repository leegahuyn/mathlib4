from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "d184ee500fb6d514db79e50d4ed581cba0123660e0f8288d6f479e6f1c63d51f"
EXPECTED_OUTPUT_SHA256 = "5f7052b75353817e55e4fab35cc5f6578a9449737476a3dd05621999eaa67eed"
EXPECTED_DOT_CONTINUATIONS = 88
EXPECTED_TUPLE_REPAIRS = 21


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def repair_parser_frontier(source: str) -> tuple[str, int, int]:
    """Repair parser-invalid field continuations and typed pair endpoints.

    The scanner deliberately leaves nested comments, line comments, and strings
    byte-for-byte unchanged. Only executable Lean text is normalized.
    """

    typed_pair = "(1 / 2 : ℝ, 1)"
    repaired_pair = "((1 / 2 : ℝ), 1)"
    out: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    in_line_comment = False
    dot_count = 0
    pair_count = 0

    while index < len(source):
        if in_line_comment:
            character = source[index]
            out.append(character)
            index += 1
            if character == "\n":
                in_line_comment = False
            continue

        if block_depth:
            if source.startswith("/-", index):
                out.append("/-")
                block_depth += 1
                index += 2
            elif source.startswith("-/", index):
                out.append("-/")
                block_depth -= 1
                index += 2
            else:
                out.append(source[index])
                index += 1
            continue

        if in_string:
            character = source[index]
            out.append(character)
            index += 1
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            continue

        if source.startswith("--", index):
            out.append("--")
            index += 2
            in_line_comment = True
            continue
        if source.startswith("/-", index):
            out.append("/-")
            index += 2
            block_depth = 1
            continue
        if source[index] == '"':
            out.append('"')
            index += 1
            in_string = True
            continue

        if source.startswith(typed_pair, index):
            out.append(repaired_pair)
            index += len(typed_pair)
            pair_count += 1
            continue

        if source[index] == "." and source.startswith(".\n", index):
            lookahead = index + 2
            while lookahead < len(source) and source[lookahead] in " \t":
                lookahead += 1
            match = re.match(r"[A-Za-z_][A-Za-z0-9_]*", source[lookahead:])
            if match is not None:
                identifier = match.group(0)
                out.append("." + identifier)
                index = lookahead + len(identifier)
                dot_count += 1
                continue

        out.append(source[index])
        index += 1

    if block_depth or in_string:
        raise RuntimeError("unterminated comment or string while repairing parser frontier")
    return "".join(out), dot_count, pair_count


def main() -> int:
    source = TARGET.read_text(encoding="utf-8")
    input_sha = digest(source)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass322-r3] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass322-r3 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    repaired, dot_count, pair_count = repair_parser_frontier(source)
    print(f"parser field continuations repaired={dot_count}")
    print(f"typed pair endpoints repaired={pair_count}")
    if dot_count != EXPECTED_DOT_CONTINUATIONS:
        raise RuntimeError(
            f"expected {EXPECTED_DOT_CONTINUATIONS} field continuations, found {dot_count}"
        )
    if pair_count != EXPECTED_TUPLE_REPAIRS:
        raise RuntimeError(
            f"expected {EXPECTED_TUPLE_REPAIRS} typed pair endpoints, found {pair_count}"
        )

    output_sha = digest(repaired)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass322-r3 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(repaired, encoding="utf-8")
    print("[pass322-r3] FunctionalAnalysis parser frontier repaired from PASS 320 lineage")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
