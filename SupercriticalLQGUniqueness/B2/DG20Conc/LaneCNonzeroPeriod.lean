import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCOrientedCornerCrosscut
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCEssentialLoop

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneC_nonzero_integer_period
    {M₀ M₁ : ℂ} {n : ℤ} (hn : n ≠ 0)
    (hperiod : M₁ - M₀ = (n : ℂ) * (2 * Real.pi * Complex.I)) :
    2 * Real.pi ≤ (M₁ - M₀).im ∨
      (M₁ - M₀).im ≤ -(2 * Real.pi) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have him : (M₁ - M₀).im = (n : ℝ) * (2 * Real.pi) := by
    rw [hperiod]
    simp [Complex.mul_im, Complex.mul_re]
  have hsign : (1 : ℤ) ≤ n ∨ n ≤ -1 := by omega
  rcases hsign with hpos | hneg
  · left
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
    rw [him]
    nlinarith [mul_nonneg (sub_nonneg.mpr hnreal) hπ.le]
  · right
    have hnreal : (n : ℝ) ≤ -1 := by exact_mod_cast hneg
    rw [him]
    nlinarith [mul_nonneg (sub_nonneg.mpr (neg_le_neg hnreal)) hπ.le]

 

theorem laneC_nonzero_loop_lift_period
    (G : C(unitInterval, ℂ)) (hG : ∀ u, G u ≠ 0)
    (hclosed : G 0 = G 1)
    (hdeg : QuantumZipper.CA.Topo.loopDeg G hG ≠ 0)
    {M : unitInterval → ℂ} (hM : Continuous M)
    (hMexp : ∀ u, Complex.exp (M u) = G u) :
    2 * Real.pi ≤ (M 1 - M 0).im ∨
      (M 1 - M 0).im ≤ -(2 * Real.pi) := by
  exact laneC_nonzero_integer_period hdeg
    (QuantumZipper.CA.Topo.loopDeg_eq_of_lift G hG hclosed hM hMexp)

end SupercriticalLQGUniqueness.B2.DG20Conc
