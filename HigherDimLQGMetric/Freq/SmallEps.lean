import HigherDimLQGMetric.Freq.ProbBridge

/-! One threshold controls the two error probabilities and endpoint loss. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Filter Topology

/-- A common small-scale threshold for the frequency estimate. -/
theorem s4c_choose_epsilon
    {α aexp β U gap Cmod Ccov ε₁ : ℝ}
    (hα : 0 < α) (haexp : 0 < aexp) (hβ : 0 < β)
    (hU : 0 < U) (hgap : 0 < gap)
    (hCmod : 0 ≤ Cmod) (hCcov : 0 ≤ Ccov) (hε₁ : 0 < ε₁) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ε < (1 / 64 : ℝ) ∧ ε < 1 / 8 ∧ 8 * ε < β ∧ ε < ε₁ ∧
      β / 10 + Cmod * (8 * ε) ^ aexp + Ccov * ε < β ∧
      2 * U * (8 * ε) ^ α < gap * β := by
  let f : ℝ → ℝ := fun ε =>
    Cmod * (8 * ε) ^ aexp + Ccov * ε + 2 * U * (8 * ε) ^ α
  have hpowA : Continuous (fun ε : ℝ => (8 * ε) ^ α) :=
    (Real.continuous_rpow_const hα.le).comp (continuous_const.mul continuous_id)
  have hpowE : Continuous (fun ε : ℝ => (8 * ε) ^ aexp) :=
    (Real.continuous_rpow_const haexp.le).comp (continuous_const.mul continuous_id)
  have hf : Continuous f :=
    ((continuous_const.mul hpowE).add (continuous_const.mul continuous_id)).add
      (continuous_const.mul hpowA)
  have hf0 : f 0 = 0 := by
    simp [f, Real.zero_rpow hα.ne', Real.zero_rpow haexp.ne']
  let target : ℝ := min (9 * β / 10) (gap * β)
  have htarget : 0 < target := lt_min (by positivity) (mul_pos hgap hβ)
  have hevent : ∀ᶠ ε : ℝ in 𝓝 0, f ε < target := by
    have hlim : Tendsto f (𝓝 0) (𝓝 0) := by simpa only [hf0] using hf.tendsto 0
    exact hlim.eventually (gt_mem_nhds htarget)
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.1 hevent
  let ε₀ := min δ (min ε₁ (min (1 / 64) (min (1 / 8) (β / 8))))
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  have hδsmall : ε < δ := hεsmall.trans_le (by dsimp [ε₀]; exact min_le_left _ _)
  have hfsmall : f ε < target := hδf (by simpa [Real.dist_eq, abs_of_pos hε] using hδsmall)
  have hpowAn : 0 ≤ (8 * ε) ^ α := (Real.rpow_pos_of_pos (by positivity) _).le
  have hpowEn : 0 ≤ (8 * ε) ^ aexp := (Real.rpow_pos_of_pos (by positivity) _).le
  have hterms : 0 ≤ Cmod * (8 * ε) ^ aexp ∧
      0 ≤ Ccov * ε ∧ 0 ≤ 2 * U * (8 * ε) ^ α := by
    constructor
    · exact mul_nonneg hCmod hpowEn
    constructor
    · exact mul_nonneg hCcov hε.le
    · positivity
  have hε₁small : ε < ε₁ := hεsmall.trans_le (by
    dsimp [ε₀]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hε64 : ε < (1 / 64 : ℝ) := hεsmall.trans_le (by
    dsimp [ε₀]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε8 : ε < (1 / 8 : ℝ) := hεsmall.trans_le (by
    dsimp [ε₀]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hεβ : 8 * ε < β := by
    have hbound : ε < β / 8 := hεsmall.trans_le (by
      dsimp [ε₀]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))
    linarith
  refine ⟨hε64, hε8, hεβ, hε₁small, ?_, ?_⟩
  · have hft : Cmod * (8 * ε) ^ aexp + Ccov * ε < 9 * β / 10 := by
      have h := hfsmall.trans_le (min_le_left _ _)
      dsimp [f] at h
      linarith only [h, hterms.2.2]
    linarith only [hft]
  · have h := hfsmall.trans_le (min_le_right _ _)
    dsimp [f, target] at h
    linarith only [h, hterms.1, hterms.2.1]

end HigherDimLQGMetric
