import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateSum

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_rate_sum_T_large (a ζ : ℝ) (ha : 0 < a) (hζ : 0 < ζ) :
    ∃ H : ℝ, 3 ≤ H ∧
      ∀ T : ℝ, Real.exp H ≤ T → ∀ n : ℕ,
        ∑ k ∈ Finset.range n,
          (4 : ℝ) ^ k * Real.exp
            (-a * ((Real.log (T *
              (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))) ^ 2 /
              Real.log (Real.log (T *
                (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))))) ≤
        2 * Real.exp (-(a / 2) *
          ((Real.log T) ^ 2 / Real.log (Real.log T))) := by
  let α : ℝ := (ζ / 2) * Real.log 2
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨H, hH, hsum⟩ := pt_dist_rate_sum_large a α ha hα
  refine ⟨H, hH, ?_⟩
  intro T hT n
  have hT0 : 0 < T := (Real.exp_pos H).trans_le hT
  have hlogT : H ≤ Real.log T := (Real.le_log_iff_exp_le hT0).2 hT
  have hlog (k : ℕ) :
      Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))) =
        Real.log T + α * (k : ℝ) := by
    rw [Real.log_mul hT0.ne' (by positivity), Real.log_rpow (by norm_num)]
    dsimp [α]
    ring
  simpa only [hlog] using hsum (Real.log T) hlogT n

end SupercriticalLQGUniqueness.B2.DG20Pt
