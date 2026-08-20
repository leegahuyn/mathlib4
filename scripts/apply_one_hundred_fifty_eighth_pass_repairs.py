from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Mock2.lean")


REPAIRS = (
    (
        """theorem nablaTensorId_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (nablaTensorId P V z) =
      nablaTensorId P U ((aqPresheaf E F).res hUV z) := by
  rw [nablaTensorId_localTrivialization,
""",
        """theorem nablaTensorId_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (nablaTensorId P V z) =
      nablaTensorId P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (nablaTensorId P V z) =
      nablaTensorId P U ((aqPresheaf E F).res hUV z)
  rw [nablaTensorId_localTrivialization,
""",
        "Mock2 expose tensor restriction before nabla naturality",
    ),
    (
        """theorem idTensorDq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (idTensorDq P V z) =
      idTensorDq P U ((aqPresheaf E F).res hUV z) := by
  rw [idTensorDq_localTrivialization,
""",
        """theorem idTensorDq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (idTensorDq P V z) =
      idTensorDq P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (idTensorDq P V z) =
      idTensorDq P U ((aqPresheaf E F).res hUV z)
  rw [idTensorDq_localTrivialization,
""",
        "Mock2 expose tensor restriction before logarithmic naturality",
    ),
    (
        """theorem Dq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z) := by
  rw [Dq_apply, Dq_apply, map_add, nablaTensorId_restrict,
""",
        """theorem Dq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z)
  rw [Dq_apply, Dq_apply, map_add, nablaTensorId_restrict,
""",
        "Mock2 expose tensor restriction before full derivative naturality",
    ),
)


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    for old, new, label in REPAIRS:
        count = text.count(old)
        if count != 1:
            print(f"{label}: expected 1 occurrence, found {count}")
            return 1
        text = text.replace(old, new, 1)
        print(f"{label}: applied 1")
    PATH.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
