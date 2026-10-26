import SupercriticalConformalCovariance.Small.RecoveryAdapter

set_option autoImplicit false
noncomputable section
open Filter Topology
namespace SupercriticalConformalCovariance.Small

theorem dyadic_eq_inv_pow (j : ℕ) :
    SupercriticalConformalCovariance.Regular.dyadic j = ((2 : ℝ)⁻¹) ^ j := by
  simp only [SupercriticalConformalCovariance.Regular.dyadic, zpow_neg, zpow_natCast, inv_pow]

theorem dyadic_pos (j : ℕ) : 0 < SupercriticalConformalCovariance.Regular.dyadic j := by
  rw [dyadic_eq_inv_pow]
  positivity

theorem dyadic_tendsto_zero :
    Tendsto SupercriticalConformalCovariance.Regular.dyadic atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun j : ℕ => SupercriticalConformalCovariance.Regular.dyadic j) atTop (𝓝 (0 : ℝ))
  simp_rw [dyadic_eq_inv_pow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem exists_small_dyadic_offset {α : ℝ} (hα : α < 1) :
    ∃ J : ℕ, ∀ j : ℕ,
      0 < SupercriticalConformalCovariance.Regular.dyadic (j + J) ∧
      SupercriticalConformalCovariance.Regular.dyadic (j + J) ≤ (1 - α) ^ 2 ∧
      SupercriticalConformalCovariance.Regular.dyadic (j + J) < 1 := by
  have hα0 : 0 < (1 - α) ^ 2 := sq_pos_of_pos (sub_pos.mpr hα)
  have hev : ∀ᶠ j in atTop,
      SupercriticalConformalCovariance.Regular.dyadic j < min ((1 - α) ^ 2) 1 :=
    dyadic_tendsto_zero.eventually (gt_mem_nhds (lt_min hα0 one_pos))
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hev
  refine ⟨J, fun j => ⟨dyadic_pos _, ?_, ?_⟩⟩
  · exact (hJ _ (Nat.le_add_left J j)).le.trans (min_le_left _ _)
  · exact (hJ _ (Nat.le_add_left J j)).trans_le (min_le_right _ _)

end SupercriticalConformalCovariance.Small
