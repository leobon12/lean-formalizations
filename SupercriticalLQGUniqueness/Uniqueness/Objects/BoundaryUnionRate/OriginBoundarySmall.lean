import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.OriginSmallMoment




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem origin_boundary_moment_small
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hpcrit : p < 2 * Q / ξ) :
    ∃ C : ENNReal, C < ∞ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (w : ℂ) (hw : w ≠ 0),
          (∫⁻ ω,
            ((D (h ω)).internal (Metric.closedBall 0 ‖w‖)
              (⟨w, by simp only [Metric.mem_closedBall, dist_zero_right, le_refl]⟩,
               ⟨0, Metric.mem_closedBall_self (norm_nonneg w)⟩) /
              Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ 0) ^ p ∂P) ≤ C := by
  obtain ⟨C, hC, hsum⟩ :=
    origin_dyadic_sum_moment_small ξ Q hQ D hD p hp hp1 hpcrit
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh w hw
  have hbar := BiLipschitz.Barrier.ae_barrier hD hQ P h hh
  have hpoint : ∀ᵐ ω ∂P,
      (D (h ω)).internal (Metric.closedBall 0 ‖w‖)
          (⟨w, by simp only [Metric.mem_closedBall, dist_zero_right, le_refl]⟩,
           ⟨0, Metric.mem_closedBall_self (norm_nonneg w)⟩) /
            Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ 0 ≤
        ∑' i : ℕ × Bool,
          Objects.BoundaryUnionMoments.dyadicAround (D (h ω)) w i /
            Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ 0 := by
    filter_upwards [hbar] with ω hB
    have hdyad := Objects.BoundaryUnionMoments.dyadic_internal_le_around_sum_all
      (D (h ω)) hB w hw
    have hdiv := ENNReal.div_le_div_right hdyad
      (Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ 0)
    simpa only [div_eq_mul_inv, ENNReal.tsum_mul_right] using hdiv
  calc
    (∫⁻ ω,
      ((D (h ω)).internal (Metric.closedBall 0 ‖w‖)
        (⟨w, by simp only [Metric.mem_closedBall, dist_zero_right, le_refl]⟩,
         ⟨0, Metric.mem_closedBall_self (norm_nonneg w)⟩) /
        Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ 0) ^ p ∂P) ≤
        ∫⁻ ω, (∑' i : ℕ × Bool,
          Objects.BoundaryUnionMoments.dyadicAround (D (h ω)) w i /
            Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ 0) ^ p ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hpoint] with ω hω
      exact ENNReal.rpow_le_rpow hω hp.le
    _ ≤ C := hsum P h hh w hw


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
