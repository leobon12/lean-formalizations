import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic.InfiniteConcat




 




set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic

private theorem dist_smul_smul (w : ℂ) (s t : ℝ) :
    dist (s • w) (t • w) = |s - t| * ‖w‖ := by
  rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]

theorem left_inner_disk (w : ℂ) (hw : w ≠ 0) (q t : ℝ)
    (hlo : q / 2 < t) (hhi : t < 3 * q / 2) :
    t • w ∈ ball (q • w) (q * ‖w‖ / 2) := by
  have habs : |t - q| < q / 2 := abs_lt.mpr (by constructor <;> linarith)
  rw [mem_ball, dist_smul_smul]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  nlinarith [mul_lt_mul_of_pos_right habs hwpos]

theorem right_inner_disk (w : ℂ) (hw : w ≠ 0) (q t : ℝ)
    (hlo : 1 - 3 * q / 2 < t) (hhi : t < 1 - q / 2) :
    t • w ∈ ball ((1 - q) • w) (q * ‖w‖ / 2) := by
  have habs : |t - (1 - q)| < q / 2 := abs_lt.mpr (by constructor <;> linarith)
  rw [mem_ball, dist_smul_smul]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  nlinarith [mul_lt_mul_of_pos_right habs hwpos]

 

theorem dyadic_twoEnd_inner_disk_cover (w : ℂ) (hw : w ≠ 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ k : ℕ,
      t • w ∈ ball (((1 / 2 : ℝ) ^ (k + 1)) • w)
        (((1 / 2 : ℝ) ^ (k + 1)) * ‖w‖ / 2) ∨
      t • w ∈ ball ((1 - (1 / 2 : ℝ) ^ (k + 1)) • w)
        (((1 / 2 : ℝ) ^ (k + 1)) * ‖w‖ / 2) := by
  obtain ⟨k, hleft | hright⟩ := Toolkit.PaidPathCompactness.dyadic_twoEnd_interval_cover ht
  · refine ⟨k, Or.inl ?_⟩
    have hpow : (1 / 2 : ℝ) ^ (k + 2) =
        ((1 / 2 : ℝ) ^ (k + 1)) / 2 := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow] at hleft
    exact left_inner_disk w hw _ t hleft.1 (by linarith [hleft.2])
  · refine ⟨k, Or.inr ?_⟩
    have hpow : (1 / 2 : ℝ) ^ (k + 2) =
        ((1 / 2 : ℝ) ^ (k + 1)) / 2 := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow] at hright
    exact right_inner_disk w hw _ t (by linarith [hright.1]) hright.2


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic
