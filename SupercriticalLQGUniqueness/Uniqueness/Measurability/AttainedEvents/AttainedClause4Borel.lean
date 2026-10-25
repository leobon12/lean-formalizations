import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.AttainedEvent
import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.HEventUM




 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

private def shortAnnulus (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) :
    EuclideanAnnulus :=
  ⟨(z, ((a : ℝ) * r, r)), by
    have hr : 0 < (r : ℝ) := r.2
    have hq : (q : ℝ) < 1 / 100 := q.2.2
    have ha : 1 - (q : ℝ) < a := a.2.1
    have ha1 : (a : ℝ) < 1 := a.2.2
    constructor <;> nlinarith⟩

 
theorem attainedClause4_measurable (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) :
    MeasurableSet {D : LSCMetric |
      aroundDist D (shortAnnulus z r q a) ≤
        ENNReal.ofReal (K : ℝ) * acrossDist D (shortAnnulus z r q a)} := by
  let A := shortAnnulus z r q a
  have hAround : Measurable (fun D : LSCMetric => aroundDist D A) :=
    Toolkit.CountableBase.aroundBoundedAnnulus_borel A
  have hAcross : Measurable (fun D : LSCMetric => acrossDist D A) :=
    measurable_acrossDist A
  exact measurableSet_le hAround (measurable_const.mul hAcross)

theorem attainedClause4_field_measurable
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) :
    MeasurableSet {g : LQGMetric.DistC |
      aroundDist (D g) (shortAnnulus z r q a) ≤
        ENNReal.ofReal (K : ℝ) * acrossDist (D g) (shortAnnulus z r q a)} :=
  (attainedClause4_measurable z r q a K).preimage hD

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
