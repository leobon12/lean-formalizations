/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImageUniform
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# The amalgamated charge in the opposite view

Packet PROVE-ZHAN-GT4-A22. At own height zero all original seed locations
coincide at the other source. Their opposite-view charges add to the
other-source charge. This file records the exact algebra and constructs
that one-force base evolution using the landed Theorem 2.2.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

/-- The opposite curve's charge at the amalgamated original source. -/
def mirrorSourceCharge {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) : ℝ :=
  -8 / κ - 4 * ∑ m, rr m

/-- Opposite charges `κ₂ r₂,m`, with `κ₂=16/κ` and `r₂,m=-(κ/4)r_m`,
combine with `-κ₂/2` to give the amalgamated source charge. -/
theorem mirrorSourceCharge_eq {n : ℕ} {κ : ℝ} (hκ : κ ≠ 0) (rr : Fin n → ℝ) :
    -(16 / κ) / 2 + ∑ m, (16 / κ) * (-(κ / 4) * rr m) = mirrorSourceCharge κ rr := by
  have he : ∀ m, (16 / κ) * (-(κ / 4) * rr m) = -4 * rr m := fun m => by
    field_simp
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold mirrorSourceCharge
  ring

/-- The force drift of the coincident opposite-view marks is the drift
of the single amalgamated force point, also with Lean's total division. -/
theorem mirror_source_drift {n : ℕ} {κ : ℝ} (hκ : κ ≠ 0)
    (rr : Fin n → ℝ) (w v : ℝ) :
    -(16 / κ) / (2 * (w - v)) + ∑ m, (16 / κ) * (-(κ / 4) * rr m) / (w - v) =
      mirrorSourceCharge κ rr / (w - v) := by
  rw [← Finset.sum_div, ← mirrorSourceCharge_eq hκ rr]
  rw [add_div]
  have he : ∀ a b : ℝ, -a / (2 * b) = (-a / 2) / b := fun a b => by ring
  rw [he]

/-- The space field of coincident marks has the summed source exponent. -/
theorem dualLogSpace_coincident {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) (f f₁ v : ℝ) :
    dualLogSpace κ rr f f₁ v (fun _ => v) =
      dualAlpha κ * Real.log f₁ + (-1 / 2 + ∑ m, rr m) * Real.log (f - v) := by
  unfold dualLogSpace
  rw [← Finset.sum_mul]
  ring

/-- The spatial logarithmic derivative has the same amalgamation. -/
theorem dualLogSpaceX_coincident {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) (f f₁ f₂ v : ℝ) :
    dualLogSpaceX κ rr f f₁ f₂ v (fun _ => v) =
      dualAlpha κ * (f₂ / f₁) + (-1 / 2 + ∑ m, rr m) * (f₁ / (f - v)) := by
  unfold dualLogSpaceX
  rw [← Finset.sum_mul]
  ring

/-- The amalgamated opposite-view base law exists for every seed charge
configuration. The force point is separated from its own source. -/
theorem exists_mirror_amalgamated_evolution {n : ℕ} {κ p : ℝ}
    (hκ : 0 < κ) (hp : 0 < p) (rr : Fin n → ℝ) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution (16 / κ) (fun _ : Fin 1 => -p) Fin.elim0
        (fun _ => mirrorSourceCharge κ rr) Fin.elim0 P 𝓕 W VL VR B ζ := by
  have hw : IsOrderedForceWord (fun _ : Fin 1 => -p) (Fin.elim0 : Fin 0 → ℝ) :=
    ⟨fun _ _ _ => le_rfl, fun _ => neg_nonpos.2 hp.le,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  exact exists_isIntegratedSLEEvolution_assembled (div_pos (by norm_num) hκ) hw

end InteractingSLE.ZhanGT4
