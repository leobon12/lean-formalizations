import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockRelationBorel




 


set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

open LQGMetric (DistC)

theorem measurable_normTranslate (z : ℂ) : Measurable (Objects.Producer.normTranslate z) := by
  apply LQGMetric.measurable_distOn_iff.2
  intro φ
  have htr : Measurable (translateDist z) := by
    have heq : translateDist z = LQGMetric.affineComp 1 z :=
      funext fun g => Objects.Producer.translateDist_eq_affineComp_one z g
    rw [heq]
    exact LQGMetric.measurable_affineComp 1 z
  have htrφ : Measurable (fun g : DistC => translateDist z g φ) :=
    (LQGMetric.measurable_distOn_apply φ).comp htr
  have hc : Measurable (fun g : DistC => -(LQGMetric.circleAvg g 1 z)) :=
    (LQGMetric.measurable_circleAvg_left 1 z).neg
  have heq : (fun g : DistC => Objects.Producer.normTranslate z g φ) =
      (fun g : DistC => translateDist z g φ +
        (∫ x, φ x) * -(LQGMetric.circleAvg g 1 z)) := by
    funext g
    exact LQGMetric.GFFInv.addConst_apply _ _ φ
  rw [heq]
  exact htrφ.add (measurable_const.mul hc)

 

theorem blockEvent_um (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (Ksh : ℕ) (Cmid0 : ℝ)
    (D E : DistC → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (hRad : 0 ≤ T.blockRadius) (hR : 0 < T.rho * T.r)
    (hn : ‖T.orientation‖ = 1) (z : ℂ) :
    LQGMetric.UMeasurableSet {g : DistC |
      Objects.Excursions.blockEvent C T Ksh Cmid0 D E z g} := by
  have hRaw := blockRaw_um C T Ksh Cmid0 D E hD hE hRad hR hn
  change LQGMetric.UMeasurableSet
    (Objects.Producer.normTranslate z ⁻¹' {g : DistC | Objects.Excursions.blockRaw C T Ksh Cmid0 D E g})
  exact hRaw.preimage (measurable_normTranslate z)

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
