import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.AnnulusRate
import SupercriticalLQGUniqueness.Uniqueness.Objects.T58Numerics.Num




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem normalizedAroundAt_positive_rate
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp : 0 < p) (hpcrit : p < 2 * Q / ξ) :
    ∃ q : ℝ, ∃ K : ENNReal, 1 < q ∧ K < ∞ ∧
      0 < (ξ : ℝ) * Q * p - q * p ^ 2 * ξ ^ 2 / 2 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (a s : Set.Ioi (0 : ℝ)) (has : (a : ℝ) ≤ s)
          (y c : ℂ) (hnear : ‖y - c‖ ≤ s),
          (∫⁻ ω, normalizedAroundAt ξ Q D (h ω) a s y c ^ p ∂P) ≤
            K * ENNReal.ofReal
              ((a / s) ^ (ξ * Q * p - q * p ^ 2 * ξ ^ 2 / 2)) := by
  obtain ⟨q, hq, hγ⟩ := Objects.T58Numerics.holder_exponent ξ.2 hp hpcrit
  obtain ⟨K, hK, hM⟩ := normalizedAroundAt_moment_rate ξ Q hQ D hD p q hp hq
  exact ⟨q, K, hq, hK, hγ, hM⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
