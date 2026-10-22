import HigherDimLQGContinuity.Core.Interfaces

/-!
# Fixed exponential thresholds for the mesh depth
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- Any fixed positive target can be met by one lower bound on the depth. -/
theorem q11_exp_small_threshold {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ V : ℝ, L ≤ V → Real.exp (-V) ≤ δ := by
  refine ⟨max 1 (Real.log δ⁻¹), le_max_left _ _, fun V hV => ?_⟩
  have hlog : Real.log δ⁻¹ ≤ V := (le_max_right _ _).trans hV
  have hExp : Real.exp (-V) ≤ Real.exp (-(Real.log δ⁻¹)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hEq : Real.exp (-(Real.log δ⁻¹)) = δ := by
    rw [Real.exp_neg, Real.exp_log (inv_pos.mpr hδ)]
    simp
  exact hExp.trans_eq hEq

/-- A fixed prefactor in a failure bound is absorbed at sufficiently deep
mesh scale. -/
theorem q11_exp_decay_threshold {C p : ℝ} (hC : 0 < C) (hp : 0 < p) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ V : ℝ, L ≤ V → C * Real.exp (-V) ≤ p := by
  obtain ⟨L, hL, hsmall⟩ :=
    q11_exp_small_threshold (show 0 < p / C by positivity)
  refine ⟨L, hL, fun V hV => ?_⟩
  have hh := mul_le_mul_of_nonneg_left (hsmall V hV) hC.le
  have heq : C * (p / C) = p := by field_simp
  simpa only [heq] using hh

/-- The same threshold with an arbitrary fixed positive exponential rate. -/
theorem q11_exp_decay_rate_threshold {C p c : ℝ}
    (hC : 0 < C) (hp : 0 < p) (hc : 0 < c) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ V : ℝ, L ≤ V → C * Real.exp (-(c * V)) ≤ p := by
  obtain ⟨L0, hL0, hsmall⟩ := q11_exp_decay_threshold hC hp
  refine ⟨max 1 (L0 / c), le_max_left _ _, fun V hV => ?_⟩
  have hcv : L0 ≤ c * V := by
    have hdiv : L0 / c ≤ V := (le_max_right _ _).trans hV
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hdiv
  exact hsmall (c * V) hcv

end HigherDimLQGContinuity
