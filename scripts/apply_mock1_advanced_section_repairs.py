from pathlib import Path

path = Path("PrimalitySheafVerification/Mock1_Advanced.lean")
text = path.read_text(encoding="utf-8")

names = [
    "objectSchemaRequirements",
    "t1t5Requirements",
    "sptRequirements",
    "kernelRequirements",
    "exactCoefficientRequirements",
    "pAdicRequirements",
    "entropyReproRequirements",
    "finalInstanceRequirements",
]

changed = 0
for name in names:
    old = f"  cases r <;>\n    simp [{name}, sectionOf] at h ⊢"
    new = f"  cases r <;>\n    simp_all [{name}, sectionOf]"
    if old in text:
        text = text.replace(old, new, 1)
        changed += 1
    elif new not in text:
        raise SystemExit(f"expected section proof not found: {name}")

path.write_text(text, encoding="utf-8", newline="\n")
print(f"updated {changed} section membership proofs")
