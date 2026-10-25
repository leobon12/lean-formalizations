import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit




 





set_option autoImplicit false
noncomputable section
open Set Metric
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls

theorem neighboring_separators_intersect {K K' : Set ℂ} {z u : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hu : ‖u‖ = 1)
    (hK : LQGMetric.Disconnects K (Metric.sphere z ρ)
      (Metric.sphere z (2 * ρ)))
    (hK' : LQGMetric.Disconnects K'
      (Metric.sphere (z + (3 / 2 * ρ) • u) ρ)
      (Metric.sphere (z + (3 / 2 * ρ) • u) (2 * ρ)))
    (hpc : IsPathConnected K') : (K ∩ K').Nonempty := by
  let z' : ℂ := z + (3 / 2 * ρ) • u
  have hρ2 : ρ ≤ 2 * ρ := by linarith
  obtain ⟨tL, htL⟩ :=
    Toolkit.PlanarSeparation.disconnects_meets_radial_segment hρ.le hρ2
      (u := -u) (by simpa using hu) hK'
  obtain ⟨tR, htR⟩ :=
    Toolkit.PlanarSeparation.disconnects_meets_radial_segment hρ.le hρ2
      (u := u) hu hK'
  let sL : ℝ := ρ + (tL : ℝ) * ρ
  let sR : ℝ := ρ + (tR : ℝ) * ρ
  have hsL : ρ ≤ sL ∧ sL ≤ 2 * ρ := by
    dsimp [sL]
    have ht := tL.property
    constructor <;> nlinarith [mul_nonneg ht.1 hρ.le,
      mul_nonneg (sub_nonneg.mpr ht.2) hρ.le]
  have hsR : ρ ≤ sR ∧ sR ≤ 2 * ρ := by
    dsimp [sR]
    have ht := tR.property
    constructor <;> nlinarith [mul_nonneg ht.1 hρ.le,
      mul_nonneg (sub_nonneg.mpr ht.2) hρ.le]
  have hleft_eq : Path.segment (z' + ρ • (-u)) (z' + (2 * ρ) • (-u)) tL =
      z + (3 / 2 * ρ - sL) • u := by
    rw [Toolkit.PlanarSeparation.radial_segment_formula]
    dsimp [z', sL]
    push_cast
    ring
  have hright_eq : Path.segment (z' + ρ • u) (z' + (2 * ρ) • u) tR =
      z + (3 / 2 * ρ + sR) • u := by
    rw [Toolkit.PlanarSeparation.radial_segment_formula]
    dsimp [z', sR]
    push_cast
    ring
  have hleft : (K' ∩ Metric.closedBall z ρ).Nonempty := by
    refine ⟨z + (3 / 2 * ρ - sL) • u, ?_, ?_⟩
    · rw [← hleft_eq]
      exact htL
    · change dist (z + (3 / 2 * ρ - sL) • u) z ≤ ρ
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hsL.2], by linarith [hsL.1]⟩
  have hright : (K' ∩ (Metric.ball z (2 * ρ))ᶜ).Nonempty := by
    refine ⟨z + (3 / 2 * ρ + sR) • u, ?_, ?_⟩
    · rw [← hright_eq]
      exact htR
    · change ¬ dist (z + (3 / 2 * ρ + sR) • u) z < 2 * ρ
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (by linarith [hsR.1])]
      linarith [hsR.1]
  exact Toolkit.PlanarSeparation.disconnects_meets_pathConnected_crossing hρ2 hK hpc hleft hright

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls
