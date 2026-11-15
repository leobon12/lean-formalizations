/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Patched

/-!
# The full seeded Eight statement reduced to its image-law input alone

PROVE-ZHAN-GT4-A22. The actual patched cofinal rectangles' measurability is proved
in `DualSeedJoint2Patched`; A1-ASSEMBLE supplies the remaining marginal and exit
constructions. The existing exact named `(I2)` input `EightRectLaw` remains.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4.A1Asm
open A1Marg A1Common A1EightSeed

/-- A.1's full rectangle-wise seeded Eight input, with only the exact existing
image-law identification assumption remaining. Null patching, rectangles,
columns, rows, and their joint measurability are all constructed. -/
theorem a1DualCouplingEightSeedMStatement_of_rectLaw {κ : ℝ} (hL : EightRectLaw κ) :
    A1DualCouplingEightSeedMStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  obtain ⟨W₁', VL₁', VR₁', B₁', ζ₁', hp₁⟩ := exists_isPatchOf h₁ GoodSmallEight (ae_goodSmallEight hκ8 hx h₁)
  obtain ⟨W₂', VL₂', VR₂', B₂', ζ₂', hp₂⟩ :=
    exists_isPatchOf h₂ (fun _ _ _ _ _ => True) (Eventually.of_forall fun _ => trivial)
  obtain ⟨-, -, -, h₁', hB₁', hg₁', -⟩ := id hp₁
  obtain ⟨-, -, -, h₂', hB₂', -, -⟩ := id hp₂
  exact seedFieldInputM_of_patched hκ8 hx h₁' hB₁' hg₁' h₂' hB₂'
    (isFieldMeas_eight_of_patched hκ8 hx h₁' hB₁' hg₁' h₂' hB₂')
    (fun hs₁ hs₂ μ hμ hμ₁ hμ₂ hd => hL hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁
      VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd)


end InteractingSLE.ZhanGT4.A1Asm
