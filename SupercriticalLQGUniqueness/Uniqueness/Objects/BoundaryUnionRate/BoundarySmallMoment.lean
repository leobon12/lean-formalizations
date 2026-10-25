import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.BoundaryLaw




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem boundary_moment_small
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hpcrit : p < 2 * Q / ξ) :
    ∃ C : ENNReal, C < ∞ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (c w : ℂ) (_hw : w ≠ 0),
          (∫⁻ ω,
            ((D (h ω)).internal (Metric.closedBall c ‖w‖)
              (⟨w + c, by simp only [Metric.mem_closedBall, dist_eq_norm,
                  add_sub_cancel_right, le_refl]⟩,
               ⟨c, Metric.mem_closedBall_self (norm_nonneg w)⟩) /
              Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ c) ^ p ∂P) ≤ C := by
  obtain ⟨C, hC, hOrigin⟩ :=
    origin_boundary_moment_small ξ Q hQ D hD p hp hp1 hpcrit
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh c w hw
  let hz : Ω → LQGMetric.DistC := TwoScale.S36.recentredTranslate h c
  have hhz : IsNormalizedWholePlaneGFF hz P :=
    normalized_translate_sub_circleAvg hh c
  have heq := ae_normalized_boundary_translate P h hh ξ Q D hD c w hw
  calc
    (∫⁻ ω,
      ((D (h ω)).internal (Metric.closedBall c ‖w‖)
        (⟨w + c, by simp only [Metric.mem_closedBall, dist_eq_norm,
            add_sub_cancel_right, le_refl]⟩,
         ⟨c, Metric.mem_closedBall_self (norm_nonneg w)⟩) /
        Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ c) ^ p ∂P) =
      ∫⁻ ω,
        ((D (hz ω)).internal (Metric.closedBall 0 ‖w‖)
          (⟨w, by simp only [Metric.mem_closedBall, dist_zero_right, le_refl]⟩,
           ⟨0, Metric.mem_closedBall_self (norm_nonneg w)⟩) /
          Objects.AnnulusTails.nrm ξ Q (hz ω) ‖w‖ 0) ^ p ∂P := by
        apply lintegral_congr_ae
        filter_upwards [heq] with ω hω
        exact congrArg (· ^ p) hω
    _ ≤ C := hOrigin P hz hhz w hw


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
