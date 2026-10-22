import HigherDimLQGMetric.Growth.DyadicCells
import Mathlib.Analysis.PSeries

/-!
# Borel--Cantelli estimates for dyadic sphere-average blocks

The bounds are stated for real measures so they can be applied to both Gaussian point tails
and the compact block tails of `Sphere.Tail`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace HigherDimLQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- First Borel--Cantelli with an arbitrary summable real majorant. -/
theorem l2a_ae_eventually_of_summable_bound [IsProbabilityMeasure P]
    {E : ℕ → Set Ω} {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (hs : Summable f)
    (hE : ∀ k, P.real (E k) ≤ f k) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ E k := by
  apply ae_eventually_notMem
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (∑' k, f k))
    ENNReal.ofReal_ne_top ?_
  rw [ENNReal.ofReal_tsum_of_nonneg hf hs]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hE k)

/-- A uniform inverse-square tail is summable, hence violated only finitely often. -/
theorem l2a_ae_eventually_of_le_inv_sq [IsProbabilityMeasure P] {E : ℕ → Set Ω}
    {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ k : ℕ, P.real (E k) ≤ C * (((k : ℝ) + 1) ^ 2)⁻¹) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ E k := by
  apply ae_eventually_notMem
  have hs : Summable fun k : ℕ => C * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
    simpa using this.mul_left C
  refine ne_top_of_le_ne_top
    (b := ENNReal.ofReal (∑' k : ℕ, C * (((k : ℝ) + 1) ^ 2)⁻¹))
    ENNReal.ofReal_ne_top ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hE k)

/-- The square-root-logarithm threshold converts a Gaussian tail into an inverse square. -/
theorem l2a_exp_sqrt_log {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Real.exp (-c * Real.sqrt ((2 / c) * Real.log ((k : ℝ) + 1)) ^ 2) =
      (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hl : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
  have harg : 0 ≤ (2 / c) * Real.log ((k : ℝ) + 1) := by positivity
  rw [Real.sq_sqrt harg]
  have he : -c * ((2 / c) * Real.log ((k : ℝ) + 1)) =
      -Real.log (((k : ℝ) + 1) ^ 2) := by
    rw [Real.log_pow]
    field_simp
    ring
  rw [he, Real.exp_neg, Real.exp_log (by positivity)]

/-- The point-tail threshold with variance proportional to `k+1`. -/
theorem l2a_exp_point_log {v : ℝ} (hv : 0 < v) (k : ℕ) :
    Real.exp (-Real.sqrt (4 * v * ((k : ℝ) + 1) *
      Real.log ((k : ℝ) + 1)) ^ 2 / (2 * (v * ((k : ℝ) + 1)))) =
      (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hl : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
  have harg : 0 ≤ 4 * v * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) := by positivity
  rw [Real.sq_sqrt harg]
  have he : -(4 * v * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) /
      (2 * (v * ((k : ℝ) + 1))) = -Real.log (((k : ℝ) + 1) ^ 2) := by
    rw [Real.log_pow]
    field_simp
    ring
  rw [he, Real.exp_neg, Real.exp_log (by positivity)]

end HigherDimLQGMetric
