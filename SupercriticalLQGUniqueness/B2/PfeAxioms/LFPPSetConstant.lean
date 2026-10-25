import LQGMetric.Papers.DDDF.P18Scale
import LQGMetric.Papers.DFGPS.L2_6Path

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DFGPS

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem crossLenIn_add_const
    (ξ : ℝ) (φ : ℂ → ℝ) (c : ℝ) (U A B : Set ℂ) :
    crossLenIn ξ (fun z => φ z + c) U A B =
      ENNReal.ofReal (Real.exp (ξ * c)) * crossLenIn ξ φ U A B := by
  unfold crossLenIn
  simp_rw [lfppLen_add_const]
  simp only [ENNReal.mul_iInf_of_ne
    (by simp [Real.exp_pos] : ENNReal.ofReal (Real.exp (ξ * c)) ≠ 0)
    ENNReal.ofReal_ne_top]

end SupercriticalLQGUniqueness.B2.PfeAxioms
