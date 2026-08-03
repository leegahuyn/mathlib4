from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Spt4.lean")


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    old = """/-- The differential `(resC N).d (j+1+1) (j+1)` vanishes (everything above degree 0). -/
set_option maxHeartbeats 800000 in
theorem resC_d_succ_zero (N j : ℕ) : (resC N).d (j + 1 + 1) (j + 1) = 0 := by
  simpa [resC, df] using
    (ChainComplex.of_d Xf (df N)
      (fun n => by
        have : df N (n + 1) = 0 := rfl
        rw [this, zero_comp]) (j + 1))
"""
    new = """/- The differential `(resC N).d (j+1+1) (j+1)` vanishes (everything above degree 0). -/
theorem resC_d_succ_zero (N j : ℕ) : (resC N).d (j + 1 + 1) (j + 1) = 0 := by
  change ChainComplex.of.d Xf (df N) (j + 1 + 1) (j + 1) = 0
  rw [ChainComplex.of_d]
  rfl
"""
    count = text.count(old)
    if count == 1:
        PATH.write_text(text.replace(old, new), encoding="utf-8", newline="\n")
        print("Spt4 terminal differential proof: applied")
    elif count == 0:
        print("Spt4 terminal differential proof: already applied/source changed")
    else:
        raise RuntimeError(f"Spt4 terminal differential proof: expected one match, found {count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
