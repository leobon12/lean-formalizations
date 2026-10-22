import HigherDimLQGMetric.Growth.SmallTail

/-!
# Summability after the finite-grid union bound

Packet L2a. The factor `exp(-(d+2)(k+1))` beats the `O(2^(dk))` grid cardinality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem l2a_grid_card_le_exp {R : ℝ} (hR : 0 ≤ R) (k : ℕ) :
    ((HigherDimLFPP.Osc.grid (0 : Rd d) R (l2a_smallScale k)).card : ℝ) ≤
      (2 * R + 1) ^ d * Real.exp ((d : ℝ) * k) := by
  have ha := l2a_smallScale_pos k
  have hc := HigherDimLFPP.Osc.card_grid_le (0 : Rd d) hR ha
  have hbase : 2 * R / l2a_smallScale k + 1 ≤ (2 * R + 1) * (2 : ℝ) ^ k := by
    rw [l2a_smallScale, div_inv_eq_mul]
    have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpow : ((2 : ℝ) ^ k) ^ d ≤ (Real.exp 1 ^ k) ^ d := by
    gcongr
  calc ((HigherDimLFPP.Osc.grid (0 : Rd d) R (l2a_smallScale k)).card : ℝ)
      ≤ (2 * R / l2a_smallScale k + 1) ^ d := hc
    _ ≤ ((2 * R + 1) * (2 : ℝ) ^ k) ^ d := pow_le_pow_left₀ (by positivity) hbase d
    _ = (2 * R + 1) ^ d * ((2 : ℝ) ^ k) ^ d := mul_pow _ _ _
    _ ≤ (2 * R + 1) ^ d * (Real.exp 1 ^ k) ^ d :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * R + 1) ^ d * Real.exp ((d : ℝ) * k) := by
      rw [← pow_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring_nf

theorem l2a_summable_grid_tail {R : ℝ} (hR : 0 ≤ R) :
    Summable fun k : ℕ =>
      ((HigherDimLFPP.Osc.grid (0 : Rd d) R (l2a_smallScale k)).card : ℝ) *
        Real.exp (-((d : ℝ) + 2) * ((k : ℝ) + 1)) := by
  let B : ℝ := (2 * R + 1) ^ d
  have hs : Summable fun k : ℕ => B * Real.exp (-(k : ℝ)) :=
    Real.summable_exp_neg_nat.mul_left B
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_) hs
  have hc := l2a_grid_card_le_exp (d := d) hR k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have he : (d : ℝ) * k + -((d : ℝ) + 2) * ((k : ℝ) + 1) ≤ -(k : ℝ) := by
    nlinarith [mul_nonneg hd0 hk0]
  calc ((HigherDimLFPP.Osc.grid (0 : Rd d) R (l2a_smallScale k)).card : ℝ) *
        Real.exp (-((d : ℝ) + 2) * ((k : ℝ) + 1))
      ≤ B * Real.exp ((d : ℝ) * k) *
          Real.exp (-((d : ℝ) + 2) * ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = B * Real.exp ((d : ℝ) * k + -((d : ℝ) + 2) * ((k : ℝ) + 1)) := by
      rw [Real.exp_add]
      ring
    _ ≤ B * Real.exp (-(k : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_monotone he) hB

end HigherDimLQGMetric
