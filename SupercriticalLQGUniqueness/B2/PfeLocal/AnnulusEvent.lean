import SupercriticalLQGUniqueness.B2.PfeLocal.NonDawdleGeom
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus

 





set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal
open LQGMetric (DistC circleAvg)

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
def innerAnnulus (z : ℂ) (r : ℝ) (hr : 0 < r) : EuclideanAnnulus :=
  ⟨(z, r / 2, r), by constructor <;> linarith⟩

 
def outerAnnulus (z : ℂ) (r : ℝ) (hr : 0 < r) : EuclideanAnnulus :=
  ⟨(z, r, 2 * r), by constructor <;> linarith⟩

 


def annulusEvent {Ω : Type*} [MeasurableSpace Ω]
    (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (h : Ω → DistC) (D : Ω → LSCMetric)
    (z : ℂ) (r : Set.Ioi (0 : ℝ)) (C : Set.Ioi (1 : ℝ)) : Set Ω :=
  {ω | ENNReal.ofReal ((c r : ℝ) / (C : ℝ) *
      Real.exp (ξ * circleAvg (h ω) r z)) <
      acrossDist (D ω) (innerAnnulus z r r.2) ∧
      aroundDist (D ω) (outerAnnulus z r r.2) <
        ENNReal.ofReal ((C : ℝ) * (c r : ℝ) *
          Real.exp (ξ * circleAvg (h ω) r z))}

 

theorem measurableSet_annulusEvent {Ω : Type*} [MeasurableSpace Ω]
    (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (h : Ω → DistC) (D : Ω → LSCMetric)
    (hh : Measurable h) (hD : Measurable D)
    (z : ℂ) (r : Set.Ioi (0 : ℝ)) (C : Set.Ioi (1 : ℝ)) :
    MeasurableSet (annulusEvent ξ c h D z r C) := by
  have hca : Measurable fun ω => circleAvg (h ω) r z :=
    (LQGMetric.measurable_circleAvg_left r z).comp hh
  have hscale : Measurable fun ω => Real.exp (ξ * circleAvg (h ω) r z) :=
    Real.measurable_exp.comp (measurable_const.mul hca)
  have hin : Measurable fun ω =>
      acrossDist (D ω) (innerAnnulus z r r.2) :=
    (measurable_acrossDist _).comp hD
  have hout : Measurable fun ω =>
      aroundDist (D ω) (outerAnnulus z r r.2) :=
    (Uniqueness.Toolkit.CountableBase.aroundBoundedAnnulus_borel _).comp hD
  change MeasurableSet ({ω | ENNReal.ofReal
      ((c r : ℝ) / (C : ℝ) * Real.exp (ξ * circleAvg (h ω) r z)) <
      acrossDist (D ω) (innerAnnulus z r r.2)} ∩
      {ω | aroundDist (D ω) (outerAnnulus z r r.2) < ENNReal.ofReal
        ((C : ℝ) * (c r : ℝ) * Real.exp (ξ * circleAvg (h ω) r z))})
  exact (measurableSet_lt (measurable_const.mul hscale).ennreal_ofReal hin).inter
    (measurableSet_lt hout (measurable_const.mul hscale).ennreal_ofReal)

end SupercriticalLQGUniqueness.B2.PfeLocal
