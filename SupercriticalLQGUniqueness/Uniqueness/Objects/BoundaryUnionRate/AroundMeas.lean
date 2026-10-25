import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.AroundFinite
import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.CostMeas
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnion.Bad




 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem measurable_normalizedAroundCost (ξ Q : ℝ)
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    (s : Set.Ioi (0 : ℝ)) (y : ℂ) :
    Measurable (fun g => normalizedAroundCost ξ Q D g s y) := by
  unfold normalizedAroundCost
  have hs : (0 : ℝ) < s := s.2
  have ha : (0 : ℝ) < (1/2) * s := by positivity
  have hab : (1/2 : ℝ) * s < 1 * s := by nlinarith
  exact ((Objects.ClauseMeasurability.measurable_around y ((1/2) * s) (1 * s) ha hab).comp hD).div
    (Objects.BoundaryUnion.measurable_nrm ξ Q s y)


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
