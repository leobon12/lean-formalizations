import HigherDimLQGContinuity.Improve.PinWindow

/-!
# Combining site and seed pin ratios
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- Two half-budget log ratios give the full seed ratio; multiplying the
secondary seed unit by the primary-site ratio costs only one fixed factor
`exp 1` in the unit window. -/
theorem q11_seed_ratio_window {L SD SF cscale v : ℝ}
    (hL : 1 ≤ L) (hSD : 0 < SD) (hSF : 0 < SF) (hc : 0 < cscale)
    (hv1 : v ≤ 1)
    (hSDlo : L⁻¹ ≤ SD) (hSDhi : SD ≤ L)
    (hSFlo : L⁻¹ ≤ SF) (hSFhi : SF ≤ L)
    (hcLog : |Real.log cscale| ≤ v / 20)
    (hseedLog : |Real.log (SF / SD)| ≤ v / 20) :
    let Λ := Real.exp 1 * L
    Λ⁻¹ ≤ SD ∧ SD ≤ Λ ∧
      Λ⁻¹ ≤ cscale * SF ∧ cscale * SF ≤ Λ ∧
      |Real.log ((cscale * SF) / SD)| ≤ v / 10 := by
  let Λ : ℝ := Real.exp 1 * L
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hE1 : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have hcloglo : -(1 : ℝ) ≤ Real.log cscale := by
    have := (neg_le_of_abs_le hcLog)
    linarith
  have hcloghi : Real.log cscale ≤ (1 : ℝ) := by
    have := (le_of_abs_le hcLog)
    linarith
  have hclo : Real.exp (-(1 : ℝ)) ≤ cscale := by
    rw [← Real.exp_log hc]
    exact Real.exp_le_exp.mpr hcloglo
  have hchi : cscale ≤ Real.exp (1 : ℝ) := by
    rw [← Real.exp_log hc]
    exact Real.exp_le_exp.mpr hcloghi
  have hΛlo : Λ⁻¹ ≤ L⁻¹ := by
    have hΛ : L ≤ Λ := by dsimp [Λ]; nlinarith [Real.exp_pos (1 : ℝ)]
    exact (inv_le_inv₀ (lt_of_lt_of_le hLpos hΛ) hLpos).2 hΛ
  have hΛhi : L ≤ Λ := by dsimp [Λ]; nlinarith [Real.exp_pos (1 : ℝ)]
  have hΛeq : Λ⁻¹ = Real.exp (-(1 : ℝ)) * L⁻¹ := by
    dsimp [Λ]
    rw [mul_inv_rev, Real.exp_neg]
    ring
  have hSFlo0 : 0 ≤ L⁻¹ := inv_nonneg.mpr hLpos.le
  have hSElo : Λ⁻¹ ≤ cscale * SF := by
    rw [hΛeq]
    exact (mul_le_mul hclo hSFlo hSFlo0 hc.le)
  have hSEhi : cscale * SF ≤ Λ := by
    dsimp [Λ]
    exact mul_le_mul hchi hSFhi hSF.le (Real.exp_pos _).le
  have hlogEq : Real.log ((cscale * SF) / SD) =
      Real.log cscale + Real.log (SF / SD) := by
    have heq : (cscale * SF) / SD = cscale * (SF / SD) := by ring
    rw [heq, Real.log_mul hc.ne' (div_pos hSF hSD).ne']
  have hlog : |Real.log ((cscale * SF) / SD)| ≤ v / 10 := by
    rw [hlogEq]
    exact (abs_add_le _ _).trans (by linarith [hcLog, hseedLog])
  exact ⟨hΛlo.trans hSDlo, hSDhi.trans hΛhi, hSElo, hSEhi, hlog⟩

end HigherDimLQGContinuity
