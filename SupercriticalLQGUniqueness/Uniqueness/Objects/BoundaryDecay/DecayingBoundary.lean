import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.AngleSmallUnion




 





set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay

theorem expected_bad_angle_mass_decays
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ENNReal, C < ∞ ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∀ (c : ℂ) (s R : ℝ) (hs : 0 < s) (_hR : 0 < R),
          (∫⁻ g, ∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs.le (g, θ)
            ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) ∂μ) ≤
            (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) Set.univ *
              (C / (ENNReal.ofReal R) ^ p) := by
  let p : ℝ := min 1 (Q / ξ)
  have hdiv : 0 < Q / (ξ : ℝ) := div_pos hQ ξ.property
  have hp : 0 < p := lt_min zero_lt_one hdiv
  have hp1 : p ≤ 1 := min_le_left _ _
  have hpcrit : p < 2 * Q / (ξ : ℝ) := by
    have hple : p ≤ Q / (ξ : ℝ) := min_le_right _ _
    rw [show 2 * Q / (ξ : ℝ) = 2 * (Q / (ξ : ℝ)) by ring]
    linarith
  obtain ⟨C, hC, hbound⟩ := Objects.BoundaryUnionRate.expected_bad_angle_mass_small ξ Q hQ D hD p hp hp1 hpcrit
  exact ⟨p, hp, C, hC, hbound⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay
