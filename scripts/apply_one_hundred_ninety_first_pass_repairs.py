from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """theorem qConnection_ext (D : AnalyticData V)
    {∇₁ ∇₂ : (sectionGaugePresheaf D).QConnection}
    (h : ∀ (U : TopologicalSpace.Opens RadiusBase)
      (s : (sectionGaugePresheaf D).Field U),
      ∇₁.D U s = ∇₂.D U s) :
    ∇₁ = ∇₂ := by
  cases ∇₁ with
  | mk D₁ h₁ =>
      cases ∇₂ with
      | mk D₂ h₂ =>
          have hD : D₁ = D₂ := by
            funext U s
            exact h U s
          cases hD
          rfl
""",
        """theorem qConnection_ext (D : AnalyticData V)
    {conn₁ conn₂ : (sectionGaugePresheaf D).QConnection}
    (h : ∀ (U : TopologicalSpace.Opens RadiusBase)
      (s : (sectionGaugePresheaf D).Field U),
      conn₁.D U s = conn₂.D U s) :
    conn₁ = conn₂ := by
  cases conn₁ with
  | mk D₁ h₁ =>
      cases conn₂ with
      | mk D₂ h₂ =>
          have hD : D₁ = D₂ := by
            funext U s
            exact h U s
          cases hD
          rfl
""",
        "Mock2 rename reserved nabla binders in qConnection_ext",
    )
    m2 = replace_exact(
        m2,
        """theorem LocalFormulaData.connection_unique {D : AnalyticData V}
    (L : LocalFormulaData D)
    (∇ : (sectionGaugePresheaf D).QConnection)
    (h : ∀ (U : TopologicalSpace.Opens RadiusBase)
      (s : (sectionGaugePresheaf D).Field U),
      ∇.D U s = L.logRadialDerivative U s + L.connectionForm U s) :
    ∇ = L.connection := by
  apply qConnection_ext D
  intro U s
  simpa using h U s
""",
        """theorem LocalFormulaData.connection_unique {D : AnalyticData V}
    (L : LocalFormulaData D)
    (conn : (sectionGaugePresheaf D).QConnection)
    (h : ∀ (U : TopologicalSpace.Opens RadiusBase)
      (s : (sectionGaugePresheaf D).Field U),
      conn.D U s = L.logRadialDerivative U s + L.connectionForm U s) :
    conn = L.connection := by
  apply qConnection_ext D
  intro U s
  simpa using h U s
""",
        "Mock2 rename reserved nabla binder in connection_unique",
    )
    m2 = replace_exact(
        m2,
        """theorem LocalFormulaData.connection_eq_iff_localFormula
    {D : AnalyticData V} (L : LocalFormulaData D)
    (∇ : (sectionGaugePresheaf D).QConnection) :
    ∇ = L.connection ↔
      ∀ (U : TopologicalSpace.Opens RadiusBase)
        (s : (sectionGaugePresheaf D).Field U),
        ∇.D U s = L.logRadialDerivative U s + L.connectionForm U s := by
  constructor
  · rintro rfl
    intro U s
    rfl
  · exact L.connection_unique ∇
""",
        """theorem LocalFormulaData.connection_eq_iff_localFormula
    {D : AnalyticData V} (L : LocalFormulaData D)
    (conn : (sectionGaugePresheaf D).QConnection) :
    conn = L.connection ↔
      ∀ (U : TopologicalSpace.Opens RadiusBase)
        (s : (sectionGaugePresheaf D).Field U),
        conn.D U s = L.logRadialDerivative U s + L.connectionForm U s := by
  constructor
  · rintro rfl
    intro U s
    rfl
  · exact L.connection_unique conn
""",
        "Mock2 rename reserved nabla binder in connection_eq_iff_localFormula",
    )
    m2 = replace_exact(
        m2,
        """theorem nablaQ_existsUnique (D : AnalyticData V) :
    ∃! ∇ : (sectionGaugePresheaf D).QConnection,
      ∀ (U : TopologicalSpace.Opens RadiusBase)
        (s : (sectionGaugePresheaf D).Field U),
        ∇.D U s = 0 := by
  refine ⟨nablaQ D, nablaQ_apply D, ?_⟩
  intro ∇ h∇
  apply qConnection_ext D
  intro U s
  calc
    ∇.D U s = 0 := h∇ U s
    _ = (nablaQ D).D U s := (nablaQ_apply D U s).symm
""",
        """theorem nablaQ_existsUnique (D : AnalyticData V) :
    ∃! conn : (sectionGaugePresheaf D).QConnection,
      ∀ (U : TopologicalSpace.Opens RadiusBase)
        (s : (sectionGaugePresheaf D).Field U),
        conn.D U s = 0 := by
  refine ⟨nablaQ D, nablaQ_apply D, ?_⟩
  intro conn hConn
  apply qConnection_ext D
  intro U s
  calc
    conn.D U s = 0 := hConn U s
    _ = (nablaQ D).D U s := (nablaQ_apply D U s).symm
""",
        "Mock2 rename reserved nabla binder in nablaQ_existsUnique",
    )
    m2 = replace_exact(
        m2,
        """theorem nablaQ_eq_iff_zeroLocalFormula (D : AnalyticData V)
    (∇ : (sectionGaugePresheaf D).QConnection) :
    ∇ = nablaQ D ↔
      ∀ (U : TopologicalSpace.Opens RadiusBase)
        (s : (sectionGaugePresheaf D).Field U),
        ∇.D U s =
          (zeroLocalFormula D).logRadialDerivative U s +
            (zeroLocalFormula D).connectionForm U s :=
  (zeroLocalFormula D).connection_eq_iff_localFormula ∇
""",
        """theorem nablaQ_eq_iff_zeroLocalFormula (D : AnalyticData V)
    (conn : (sectionGaugePresheaf D).QConnection) :
    conn = nablaQ D ↔
      ∀ (U : TopologicalSpace.Opens RadiusBase)
        (s : (sectionGaugePresheaf D).Field U),
        conn.D U s =
          (zeroLocalFormula D).logRadialDerivative U s +
            (zeroLocalFormula D).connectionForm U s :=
  (zeroLocalFormula D).connection_eq_iff_localFormula conn
""",
        "Mock2 rename reserved nabla binder in nablaQ_eq_iff_zeroLocalFormula",
    )
    m2 = replace_exact(
        m2,
        """theorem connection_unique (A : AnalyticInput D)
    (∇ : (sectionGaugePresheaf D).QConnection)
    (h∇ : ∀ (U : TopologicalSpace.Opens RadiusBase)
      (s : (sectionGaugePresheaf D).Field U),
      ∇.D U s = A.localFormula.logRadialDerivative U s +
        A.localFormula.connectionForm U s) :
    ∇ = A.connection :=
  A.localFormula.connection_unique ∇ h∇
""",
        """theorem connection_unique (A : AnalyticInput D)
    (conn : (sectionGaugePresheaf D).QConnection)
    (hConn : ∀ (U : TopologicalSpace.Opens RadiusBase)
      (s : (sectionGaugePresheaf D).Field U),
      conn.D U s = A.localFormula.logRadialDerivative U s +
        A.localFormula.connectionForm U s) :
    conn = A.connection :=
  A.localFormula.connection_unique conn hConn
""",
        "Mock2 rename reserved nabla binder in analytic connection_unique",
    )
    m2 = replace_exact(
        m2,
        """  local_formula_equivalence :
    ∀ ∇ : (sectionGaugePresheaf D).QConnection,
      ∇ = nablaQ D ↔
        ∀ (U : TopologicalSpace.Opens RadiusBase)
          (s : (sectionGaugePresheaf D).Field U),
          ∇.D U s =
            (zeroLocalFormula D).logRadialDerivative U s +
              (zeroLocalFormula D).connectionForm U s
  connection_existsUnique :
    ∃! ∇ : (sectionGaugePresheaf D).QConnection,
      ∀ (U : TopologicalSpace.Opens RadiusBase)
        (s : (sectionGaugePresheaf D).Field U),
        ∇.D U s = 0
""",
        """  local_formula_equivalence :
    ∀ conn : (sectionGaugePresheaf D).QConnection,
      conn = nablaQ D ↔
        ∀ (U : TopologicalSpace.Opens RadiusBase)
          (s : (sectionGaugePresheaf D).Field U),
          conn.D U s =
            (zeroLocalFormula D).logRadialDerivative U s +
              (zeroLocalFormula D).connectionForm U s
  connection_existsUnique :
    ∃! conn : (sectionGaugePresheaf D).QConnection,
      ∀ (U : TopologicalSpace.Opens RadiusBase)
        (s : (sectionGaugePresheaf D).Field U),
        conn.D U s = 0
""",
        "Mock2 rename reserved nabla binders in Proposition 14 certificate",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
