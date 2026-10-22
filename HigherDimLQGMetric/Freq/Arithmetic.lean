import HigherDimLQGMetric.Freq.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Arithmetic for the section 5 frequency argument

These are the three arithmetic facts from MA3 Details (c), §7.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open scoped ENNReal

/-- Equal pieces of a path of length at least `ℓs` have lengths in `[ℓs/2, ℓs]`. -/
theorem s4c_piece_bounds {L ℓs : ℝ} (hℓ : 0 < ℓs) (hL : ℓs ≤ L) :
    ℓs / 2 ≤ L / (⌈L / ℓs⌉₊ : ℝ) ∧ L / (⌈L / ℓs⌉₊ : ℝ) ≤ ℓs := by
  have hq : 1 ≤ L / ℓs := (one_le_div hℓ).2 hL
  have hc1 : L / ℓs ≤ (⌈L / ℓs⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈L / ℓs⌉₊ : ℝ) < L / ℓs + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN : (0 : ℝ) < ⌈L / ℓs⌉₊ := by linarith
  constructor
  · rw [le_div_iff₀ hN]
    have h2 : (⌈L / ℓs⌉₊ : ℝ) ≤ 2 * (L / ℓs) := by linarith
    calc ℓs / 2 * (⌈L / ℓs⌉₊ : ℝ) ≤ ℓs / 2 * (2 * (L / ℓs)) := by gcongr
      _ = L := by field_simp
  · rw [div_le_iff₀ hN]
    calc L = ℓs * (L / ℓs) := by field_simp
      _ ≤ ℓs * ⌈L / ℓs⌉₊ := by gcongr

/-- Replacing at least the fraction `θ` of a segment improves its ratio. -/
theorem s4c_step_ratio {U t θ L lam : ℝ} (htU : t ≤ U) (hθ : θ * L ≤ lam) :
    U * (L - lam) + t * lam ≤ (U - θ * (U - t)) * L := by
  nlinarith [mul_nonneg (sub_nonneg.2 htU) (sub_nonneg.2 hθ)]

/-- Outer-measure bound for subtracting a rare witness event from a regular event. -/
theorem s4c_prob_diff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F H : Set Ω)
    {δ ps p : ℝ} (hps : 0 ≤ ps) (hsum : δ + ps ≤ 1 - p)
    (h1 : ENNReal.ofReal (1 - δ) ≤ P F) (h2 : P H < ENNReal.ofReal ps) :
    ENNReal.ofReal p ≤ P (F \ H) := by
  calc ENNReal.ofReal p ≤ ENNReal.ofReal (1 - δ - ps) := ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (1 - δ) - ENNReal.ofReal ps := ENNReal.ofReal_sub _ hps
    _ ≤ P F - P H := tsub_le_tsub h1 h2.le
    _ ≤ P (F \ H) := le_measure_sdiff

end HigherDimLQGMetric
