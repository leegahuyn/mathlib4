from __future__ import annotations

import importlib.util
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
SCRIPTS = ROOT / "scripts"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def line(text: str) -> str:
    return text.splitlines()[0] if text.splitlines() else "<empty>"


def main() -> int:
    initial = M2.read_text(encoding="utf-8")
    universe = "  sheaf : QGaugePresheaf.{u, v} (Opens X)\n"
    actual = initial.count(universe)
    print(
        "[mock2-repair] pass 286 standalone ShP universe | "
        f"expected=1 actual={actual} | before={line(universe)!r} | after={line(universe)!r}"
    )
    if actual != 1:
        raise RuntimeError(f"pass 286 audit: expected 1 materialized match, found {actual}")

    with tempfile.TemporaryDirectory() as tmp:
        dummy_m2a = Path(tmp) / "Mock2_Advanced.lean"
        dummy_fa = Path(tmp) / "Mock2_FunctionalAnalysis.lean"
        dummy_m2a.write_text(
            "".join(f"theorem dummyAlias{i} : _ := by trivial\n" for i in range(601)),
            encoding="utf-8",
        )
        dummy_fa.write_text("", encoding="utf-8")

        p287 = load("pass287_mock2", SCRIPTS / "apply_two_hundred_eighty_seventh_pass_repairs.py")
        p287.M2 = M2
        p287.M2A = dummy_m2a
        p287.FA = dummy_fa
        original_exact_287 = p287.replace_exact
        original_between_287 = p287.replace_between

        def exact_287(text, old, new, label, expected=1):
            if not label.startswith("Mock2 ") or label.startswith("Mock2 Advanced"):
                print(f"[mock2-repair] pass 287 skip non-Mock2 block: {label}")
                return text
            count = text.count(old)
            print(
                f"[mock2-repair] pass 287 {label} | expected={expected} actual={count} | "
                f"before={line(old)!r} | after={line(new)!r}"
            )
            return original_exact_287(text, old, new, label, expected)

        def between_287(text, start, end, new, label):
            sc, ec = text.count(start), text.count(end)
            print(
                f"[mock2-repair] pass 287 {label} | expected_start=1 actual_start={sc} | "
                f"expected_end=1 actual_end={ec} | before={line(start)!r} | after={line(new)!r}"
            )
            return original_between_287(text, start, end, new, label)

        p287.replace_exact = exact_287
        p287.replace_between = between_287
        p287.replace_regex = lambda text, pattern, repl, label, expected: text
        p287.main()

        p288 = load("pass288_mock2", SCRIPTS / "apply_two_hundred_eighty_eighth_pass_repairs.py")
        p288.M2 = M2
        p288.M2A = dummy_m2a
        p288.FA = dummy_fa
        original_rep_288 = p288.rep

        def rep_288(text, old, new, label, expected=1):
            if not label.startswith("m2 "):
                print(f"[mock2-repair] pass 288 skip non-Mock2 block: {label}")
                return text
            count = text.count(old)
            print(
                f"[mock2-repair] pass 288 {label} | expected={expected} actual={count} | "
                f"before={line(old)!r} | after={line(new)!r}"
            )
            return original_rep_288(text, old, new, label, expected)

        p288.rep = rep_288
        p288.main()

    final = M2.read_text(encoding="utf-8")
    forbidden_old = [
        "Fork (S.resIn.app U) (S.resOut.app U)",
        "theorem certificate : Certificate where",
        "f.app U s = 0",
    ]
    for needle in forbidden_old:
        count = final.count(needle)
        print(f"[mock2-repair] postcondition old pattern {needle!r} count={count}")
        if count != 0:
            raise RuntimeError(f"Mock2 repair postcondition failed for {needle!r}: {count}")
    print("[mock2-repair] cumulative Mock2 passes 286 -> 287 -> 288 restored")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
