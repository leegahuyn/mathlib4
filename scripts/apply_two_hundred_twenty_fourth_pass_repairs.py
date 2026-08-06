from __future__ import annotations


def main() -> int:
    """No-op: the pass-224 blockers are applied atomically by pass 223."""
    print("pass 224: superseded by pass 223; no additional replacements")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
