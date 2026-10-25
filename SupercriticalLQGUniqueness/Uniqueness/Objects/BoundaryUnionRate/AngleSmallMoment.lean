import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.BoundarySmallMoment
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments.MomentToAngles




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem normalizedBoundaryCost_moment_small
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hpcrit : p < 2 * Q / ξ) :
    ∃ C : ENNReal, C < ∞ ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∀ (c : ℂ) (s : ℝ) (hs : 0 < s) (θ : ℝ),
          (∫⁻ g, Objects.BoundaryUnionMoments.normalizedBoundaryCost ξ Q D c s hs.le θ g ^ p ∂μ) ≤ C := by
  obtain ⟨C, hC, hM⟩ := boundary_moment_small ξ Q hQ D hD p hp hp1 hpcrit
  refine ⟨C, hC, ?_⟩
  intro μ _ hh c s hs θ
  let w : ℂ := circleMap c s θ - c
  have hwnorm : ‖w‖ = s := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp (circleMap_mem_sphere c hs.le θ)
  have hw : w ≠ 0 := by
    intro hzero
    have : ‖w‖ = 0 := by rw [hzero]; exact norm_zero
    linarith
  have hEq (g : LQGMetric.DistC) :
      Objects.BoundaryUnionMoments.normalizedBoundaryCost ξ Q D c s hs.le θ g =
        (D g).internal (Metric.closedBall c ‖w‖)
          (⟨w + c, by simp only [Metric.mem_closedBall, dist_eq_norm,
              add_sub_cancel_right, le_refl]⟩,
           ⟨c, Metric.mem_closedBall_self (norm_nonneg w)⟩) /
        Objects.AnnulusTails.nrm ξ Q g ‖w‖ c := by
    unfold Objects.BoundaryUnionMoments.normalizedBoundaryCost LSCMetric.internal
    simp only [hwnorm, w, sub_add_cancel]
  simp_rw [hEq]
  exact hM μ id hh c w hw


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
