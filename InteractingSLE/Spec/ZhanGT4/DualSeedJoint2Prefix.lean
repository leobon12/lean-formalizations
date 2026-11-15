/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Field

/-!
# The seeded field depends only on the original protected second prefix

PROVE-ZHAN-GT4-A22. Permits the ordinary Eight driving equation to be used only
before the protected exit, without imposing a Brownian identity after its lifetime.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4

/-- Equal original second prefixes give literally equal frozen drivers. -/
theorem frzPath_eq_of_prefix {Y : Type*} {W V : ℝ≥0 → Y → ℝ} {y : Y} {T : ℝ≥0}
    (he : ∀ u ≤ T, W u y = V u y) (p : ℝ) {t : ℝ} (_ht : 0 ≤ t) (htT : t ≤ T) :
    A1EightSeed.frzPath W p t y = A1EightSeed.frzPath V p t y := by
  funext u
  change W (max 0 (min u t)).toNNReal y + p = V (max 0 (min u t)).toNNReal y + p
  rw [he _ (Real.toNNReal_le_iff_le_coe.2
    (max_le T.coe_nonneg ((min_le_right u t).trans htT)))]

/-- Equality of the protected second prefix preserves the actual chosen Eight
records at every frozen height in the prefix, including zero. -/
theorem eightRec_eq_of_second_prefix {X Y : Type*} (κ p : ℝ) (W₁ : ℝ≥0 → X → ℝ)
    (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
    (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (x : X) {W V : ℝ≥0 → Y → ℝ} {y : Y} {T : ℝ≥0}
    (he : ∀ u ≤ T, W u y = V u y) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    A1EightSeed.eightRec κ p W₁ VL₁ VR₁ W S₁ m t (x, y) =
      A1EightSeed.eightRec κ p W₁ VL₁ VR₁ V S₁ m t (x, y) := by
  unfold A1EightSeed.eightRec
  rw [frzPath_eq_of_prefix he p ht htT]

namespace A1Patch

/-- Rectangle measurability passes through pointwise equality on the actual
rectangle; no condition is imposed outside that rectangle. -/
theorem IsFieldMeas.congr_on_unit {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {N N' : X × Y → ℝ → ℝ → ℝ} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0}
    (h : IsFieldMeas N (fun _ : Unit => S₁) (fun _ : Unit => S₂))
    (he : ∀ ω (s t : ℝ), 0 ≤ s → s ≤ S₁ ω.1 → 0 ≤ t → t ≤ S₂ ω.2 → N ω s t = N' ω s t) :
    IsFieldMeas N' (fun _ : Unit => S₁) (fun _ : Unit => S₂) := by
  intro U V hU hV hU0 hV0 hUV
  convert h U V hU hV hU0 hV0 hUV using 1
  funext ω
  obtain ⟨i, h1, h2⟩ := hUV ω
  exact (he ω (U ω) (V ω) (hU0 ω) h1 (hV0 ω) h2).symm

end A1Patch
end InteractingSLE.ZhanGT4
