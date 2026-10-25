import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Event
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations




 








set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CentreEvent

open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 
theorem map_normTranslate_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) :
    P.map (normTranslate z ∘ h) = P.map h := by
  change P.map (fun ω => LQGMetric.addConst (translateDist z (h ω))
      (-(LQGMetric.circleAvg (h ω) 1 z))) = P.map h
  exact map_normalized_translate_sub_circleAvg hh z

 
theorem map_normTranslate_fieldLaw_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) :
    (P.map h).map (normTranslate z) = P.map h := by
  have hm : Measurable (normTranslate z) := by
    change Measurable (fun u : DistC => LQGMetric.addConst (translateDist z u)
      (-(LQGMetric.circleAvg u 1 z)))
    simp only [translateDist_eq_affineComp_one]
    exact LQGMetric.DFGPS.L219.measurable_addConst_of
      (LQGMetric.measurable_affineComp 1 z)
      (LQGMetric.measurable_circleAvg_left 1 z).neg
  rw [Measure.map_map hm hh.1.measurable]
  exact map_normTranslate_eq hh z

 
theorem measure_centreTarget_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (Target : Set DistC) (hTarget : NullMeasurableSet Target (P.map h)) (z : ℂ) :
    (P.map h) (centreTarget Target z) = (P.map h) Target := by
  have hm : Measurable (normTranslate z) := by
    change Measurable (fun u : DistC => LQGMetric.addConst (translateDist z u)
      (-(LQGMetric.circleAvg u 1 z)))
    simp only [translateDist_eq_affineComp_one]
    exact LQGMetric.DFGPS.L219.measurable_addConst_of
      (LQGMetric.measurable_affineComp 1 z)
      (LQGMetric.measurable_circleAvg_left 1 z).neg
  have hqp : Measure.QuasiMeasurePreserving (normTranslate z) (P.map h) (P.map h) := by
    refine ⟨hm, ?_⟩
    rw [map_normTranslate_fieldLaw_eq hh z]
  have hc : NullMeasurableSet (centreTarget Target z) (P.map h) :=
    hTarget.preimage hqp
  calc
    (P.map h) (centreTarget Target z)
        = P (h ⁻¹' centreTarget Target z) :=
          Measure.map_apply₀ hh.1.measurable.aemeasurable hc
    _ = (P.map (normTranslate z ∘ h)) Target := by
      rw [Measure.map_apply₀ (hm.comp hh.1.measurable).aemeasurable (by
        rw [map_normTranslate_eq hh z]
        exact hTarget)]
      rfl
    _ = (P.map h) Target := by rw [map_normTranslate_eq hh z]

 
theorem measure_localRepresentative_ge {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (Target : Set DistC) (hTarget : NullMeasurableSet Target (P.map h)) (z : ℂ)
    (L : Set DistC) (hEq : L =ᵐ[P.map h] centreTarget Target z)
    (pbar : ℝ) (hprob : ENNReal.ofReal pbar ≤ (P.map h) Target) :
    ENNReal.ofReal pbar ≤ (P.map h) L := by
  rw [measure_congr hEq, measure_centreTarget_eq hh Target hTarget z]
  exact hprob

 
theorem measure_localRepresentative_sdiff_eq_zero {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (Target L : Set DistC) (z : ℂ)
    (hEq : L =ᵐ[P.map h] centreTarget Target z) :
    (P.map h) (L \ centreTarget Target z) = 0 :=
  ae_le_set.mp hEq.le

end SupercriticalLQGUniqueness.Uniqueness.Objects.CentreEvent
