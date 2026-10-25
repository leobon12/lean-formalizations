import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.DyadicGeometric




set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem measurable_normalizedAroundAt
    (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D) (a s : Set.Ioi (0 : ℝ)) (y c : ℂ) :
    Measurable (normalizedAroundAt ξ Q D · a s y c) := by
  unfold normalizedAroundAt
  have ha : (0 : ℝ) < (1 / 2) * a :=
    mul_pos (by norm_num) a.2
  have hab : (1 / 2 : ℝ) * a < 1 * a := by nlinarith [a.2]
  exact ((Objects.ClauseMeasurability.measurable_around y ((1 / 2) * a) (1 * a) ha hab).comp hD).div
    (Objects.BoundaryUnion.measurable_nrm ξ Q s c)


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
