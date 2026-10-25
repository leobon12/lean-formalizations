import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.AngleSmallMoment




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem expected_bad_angle_mass_small
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hpcrit : p < 2 * Q / ξ) :
    ∃ C : ENNReal, C < ∞ ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∀ (c : ℂ) (s R : ℝ) (hs : 0 < s) (hR : 0 < R),
          (∫⁻ g, ∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs.le (g, θ)
            ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) ∂μ) ≤
            (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) Set.univ *
              (C / (ENNReal.ofReal R) ^ p) := by
  obtain ⟨C, hC, hMoment⟩ :=
    normalizedBoundaryCost_moment_small ξ Q hQ D hD p hp hp1 hpcrit
  refine ⟨C, hC, ?_⟩
  intro μ _ hh c s R hs hR
  exact Objects.BoundaryUnionMoments.expected_bad_angle_mass_le_of_moment
    ξ Q D hD.1 μ c s R p hs hR hp C
    (fun θ => hMoment μ hh c s hs θ)


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
