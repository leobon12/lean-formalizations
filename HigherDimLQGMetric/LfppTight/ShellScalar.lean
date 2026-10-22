import HigherDimLQGMetric.LfppTight.CenteredShellTail

/-! Scalar multiplication of compact-set metric infima. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_nd_setInf_smul {d : ℕ} (A B : Set (Rd d))
    (D : C(Rd d × Rd d, ℝ)) {s : ℝ} (hs : 0 ≤ s) :
    DGZ.nd_setInf A B (s • D) = s * DGZ.nd_setInf A B D := by
  unfold DGZ.nd_setInf DGZ.nd_pairInf
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul]
  exact DGZ.nd_sInf_image_mul (A ×ˢ B) D hs

theorem l6a_medianFactor_lower {a b C ξ x L : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hC : 0 < C)
    (hmed : a ≤ C * b) (hL : |x| ≤ L) :
    (C * Real.exp (|ξ| * L))⁻¹ ≤ (b / a) * Real.exp (ξ * x) := by
  have hq : C⁻¹ ≤ b / a := by
    apply (le_div_iff₀ ha).2
    exact (inv_mul_le_iff₀ hC).2 (by simpa only [mul_comm] using hmed)
  have hξx : -( |ξ| * L) ≤ ξ * x := by
    have hmul : |ξ * x| ≤ |ξ| * L := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hL (abs_nonneg ξ)
    linarith [neg_abs_le (ξ * x)]
  have he : Real.exp (-(|ξ| * L)) ≤ Real.exp (ξ * x) :=
    Real.exp_le_exp.mpr hξx
  calc
    (C * Real.exp (|ξ| * L))⁻¹ = C⁻¹ * Real.exp (-(|ξ| * L)) := by
      rw [mul_inv_rev, Real.exp_neg]
      ring
    _ ≤ (b / a) * Real.exp (ξ * x) :=
      mul_le_mul hq he (Real.exp_pos _).le (div_nonneg hb.le ha.le)

end HigherDimLQGMetric
