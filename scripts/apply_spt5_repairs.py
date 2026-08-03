from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(path: Path, old: str, new: str, label: str) -> bool:
    text = path.read_text(encoding="utf-8")
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied or source changed")
        return False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    path.write_text(text.replace(old, new), encoding="utf-8", newline="\n")
    print(f"{label}: applied")
    return True


def main() -> int:
    path = ROOT / "Spt5.lean"
    changed = False

    changed = replace_once(
        path,
        """theorem extCotangentEquiv_one (hf : f ∈ (P.Ring)⁰) (hker : P.ker = Ideal.span {f}) :
    extCotangentEquiv P f hf hker 1
      = Extension.Cotangent.mk ⟨f, hker ▸ Ideal.mem_span_singleton_self f⟩ := by
  simp only [extCotangentEquiv, LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply,
    one_smul]
""",
        """theorem extCotangentEquiv_one (hf : f ∈ (P.Ring)⁰) (hker : P.ker = Ideal.span {f}) :
    extCotangentEquiv P f hf hker 1
      = Extension.Cotangent.mk ⟨f, hker ▸ Ideal.mem_span_singleton_self f⟩ := by
  change
    (LinearMap.toSpanSingleton S P.Cotangent
      (Extension.Cotangent.mk ⟨f, hker ▸ Ideal.mem_span_singleton_self f⟩)) 1 =
      Extension.Cotangent.mk ⟨f, hker ▸ Ideal.mem_span_singleton_self f⟩
  rw [LinearMap.toSpanSingleton_apply, one_smul]
""",
        "Spt5 expose Extension cotangent generator map",
    ) or changed

    changed = replace_once(
        path,
        """theorem he : B.e 1 = Extension.Cotangent.mk B.f := by
  rw [e, extCotangentEquiv_one]
""",
        """theorem he : B.e 1 = Extension.Cotangent.mk B.f := by
  simpa [e] using
    (extCotangentEquiv_one (P := B.P.toExtension) (f := B.f.val)
      (by simpa using B.hf) (by simpa using B.hspan))
""",
        "Spt5 transport hypersurface generator proof explicitly",
    ) or changed

    changed = replace_once(
        path,
        """theorem cotangentSpanSingletonEquiv_one (hf : f ∈ R⁰) :
    cotangentSpanSingletonEquiv f hf 1
      = (Ideal.span {f}).toCotangent ⟨f, Ideal.mem_span_singleton_self f⟩ := by
  rw [cotangentSpanSingletonEquiv, LinearEquiv.ofBijective_apply,
    LinearMap.toSpanSingleton_apply, one_smul]
""",
        """theorem cotangentSpanSingletonEquiv_one (hf : f ∈ R⁰) :
    cotangentSpanSingletonEquiv f hf 1
      = (Ideal.span {f}).toCotangent ⟨f, Ideal.mem_span_singleton_self f⟩ := by
  change
    (LinearMap.toSpanSingleton (R ⧸ Ideal.span {f}) (Ideal.span {f}).Cotangent
      ((Ideal.span {f}).toCotangent ⟨f, Ideal.mem_span_singleton_self f⟩)) 1 =
      (Ideal.span {f}).toCotangent ⟨f, Ideal.mem_span_singleton_self f⟩
  rw [LinearMap.toSpanSingleton_apply, one_smul]
""",
        "Spt5 expose principal cotangent generator map",
    ) or changed

    changed = replace_once(
        path,
        """  map_id n := by apply RingCat.hom_ext; simp [ZMod.castHom_self]
""",
        """  map_id n := by
    apply RingCat.hom_ext
    ext x
    rfl
""",
        "Spt5 prove cyclic presheaf identity pointwise",
    ) or changed

    print("Spt5 repairs changed sources." if changed else "No Spt5 changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
