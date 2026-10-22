import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Improve.Class
import HigherDimLQGContinuity.Improve.ScaleCount
import HigherDimLQGMetric.Sec8b.Lemma84Parameters

/-!
# Counting scale, colour and unit-bin classes

The class count grows quadratically in the depth `V = log Δ⁻¹`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- The exact product count is bounded by the three independent window
counts. -/
theorem q11_classSet_card_le {d : ℕ} {V Δ K0 : ℝ}
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hK0 : 0 ≤ K0) :
    ((q11ClassSet d V Δ K0).card : ℝ) ≤
      (2 * V / Real.log 2 + 1) * ((1000 * d) ^ d : ℕ) *
        (2 * K0 * Real.logb 2 Δ⁻¹ + 4) := by
  have hscale := q11_fullScales_card_le hV
  have hbin := s7b_binIndices_card_le hΔ hΔ1 hK0
  have hcolors := sec8Colors_card d
  have hcard : ((q11ClassSet d V Δ K0).card : ℝ) =
      ((p4_fullScales V).card : ℝ) * ((sec8Colors d).card : ℝ) *
        ((s7b_binIndices (Δ ^ K0) (Δ ^ (-K0))).card : ℝ) := by
    simp only [q11ClassSet, Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
    ring
  rw [hcard, hcolors]
  gcongr

/-- At `Δ = e^{-V}`, the class count is bounded by a fixed quadratic
polynomial in `1+V`. -/
theorem q11_classSet_card_exp_le {d : ℕ} {V K0 : ℝ}
    (hV : 0 ≤ V) (hK0 : 0 ≤ K0) :
    ((q11ClassSet d V (Real.exp (-V)) K0).card : ℝ) ≤
      ((1000 * d) ^ d : ℕ) *
        (2 / Real.log 2 + 1) * (2 * K0 / Real.log 2 + 4) * (1 + V) ^ (2 : ℕ) := by
  have hΔ : 0 < Real.exp (-V) := Real.exp_pos _
  have hΔ1 : Real.exp (-V) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hbase := q11_classSet_card_le (d := d) hV hΔ hΔ1 hK0
  have hlog : Real.logb 2 (Real.exp (-V))⁻¹ = V / Real.log 2 := by
    simp only [Real.logb, Real.log_inv, Real.log_exp]
    ring
  rw [hlog] at hbase
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlin1 : 2 * V / Real.log 2 + 1 ≤
      (2 / Real.log 2 + 1) * (1 + V) := by
    have hdiv : 0 ≤ 2 / Real.log 2 := by positivity
    have heq : (2 / Real.log 2 + 1) * (1 + V) =
        2 * V / Real.log 2 + 1 + 2 / Real.log 2 + V := by ring
    rw [heq]
    linarith only [hV, hdiv]
  have hlin2 : 2 * K0 * (V / Real.log 2) + 4 ≤
      (2 * K0 / Real.log 2 + 4) * (1 + V) := by
    have hdiv : 0 ≤ 2 * K0 / Real.log 2 := by positivity
    have heq : (2 * K0 / Real.log 2 + 4) * (1 + V) =
        2 * K0 * (V / Real.log 2) + 4 + 2 * K0 / Real.log 2 + 4 * V := by ring
    rw [heq]
    linarith only [hV, hdiv]
  have hC : (0 : ℝ) ≤ ((1000 * d) ^ d : ℕ) := by positivity
  have hlin1pos : 0 ≤ 2 / Real.log 2 + 1 := by positivity
  have hlin2pos : 0 ≤ 2 * K0 / Real.log 2 + 4 := by positivity
  have hB0 : 0 ≤ 2 * K0 * (V / Real.log 2) + 4 := by positivity
  have hA'0 : 0 ≤ (2 / Real.log 2 + 1) * (1 + V) := by positivity
  calc
    ((q11ClassSet d V (Real.exp (-V)) K0).card : ℝ)
        ≤ (2 * V / Real.log 2 + 1) * ((1000 * d) ^ d : ℕ) *
          (2 * K0 * (V / Real.log 2) + 4) := hbase
    _ ≤ ((1000 * d) ^ d : ℕ) *
        (2 / Real.log 2 + 1) * (2 * K0 / Real.log 2 + 4) * (1 + V) ^ (2 : ℕ) := by
          have hmul1 := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hlin1 hC) hB0
          have hmul2 := mul_le_mul_of_nonneg_left hlin2
            (mul_nonneg hA'0 hC)
          calc
            (2 * V / Real.log 2 + 1) * ((1000 * d) ^ d : ℕ) *
                (2 * K0 * (V / Real.log 2) + 4)
                ≤ (2 / Real.log 2 + 1) * (1 + V) *
                    ((1000 * d) ^ d : ℕ) * (2 * K0 * (V / Real.log 2) + 4) := hmul1
            _ ≤ (2 / Real.log 2 + 1) * (1 + V) *
                    ((1000 * d) ^ d : ℕ) *
                    ((2 * K0 / Real.log 2 + 4) * (1 + V)) := hmul2
            _ = _ := by ring

end HigherDimLQGContinuity
