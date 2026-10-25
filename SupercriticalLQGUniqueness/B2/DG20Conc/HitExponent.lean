import Mathlib.Analysis.SpecialFunctions.Pow.Real

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
def hitExponent (ξ Q : ℝ) : ℝ :=
  if ξ ≤ Q then ξ * Q - ξ ^ 2 / 2 else Q ^ 2 / 2

 


theorem hitExponent_pos {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : 0 < Q) :
    0 < hitExponent ξ Q := by
  unfold hitExponent
  split_ifs with h
  · have hprod : ξ ^ 2 ≤ ξ * Q := by nlinarith [mul_nonneg hξ.le (sub_nonneg.mpr h)]
    nlinarith [sq_pos_of_pos hξ]
  · positivity

 
theorem half_sq_le_hitExponent_of_le {ξ Q : ℝ} (hξ : 0 ≤ ξ) (h : ξ ≤ Q) :
    ξ ^ 2 / 2 ≤ hitExponent ξ Q := by
  simp only [hitExponent, if_pos h]
  nlinarith [mul_nonneg hξ (sub_nonneg.mpr h)]

 
theorem hitExponent_of_gt {ξ Q : ℝ} (h : Q < ξ) :
    hitExponent ξ Q = Q ^ 2 / 2 := by
  simp [hitExponent, not_le.mpr h]

end SupercriticalLQGUniqueness.B2.DG20Conc
