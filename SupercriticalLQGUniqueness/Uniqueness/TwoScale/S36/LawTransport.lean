import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.GProjection




 











set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 
theorem prob_preimage_eq_law_of_um {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {h : Ω → DistC} (hh : Measurable h) {S : Set DistC}
    (hS : LQGMetric.UMeasurableSet S) :
    P (h ⁻¹' S) = (P.map h) S :=
  (Measure.map_apply₀ hh.aemeasurable (hS (P.map h) inferInstance)).symm

 
theorem prob_preimage_eq_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsFiniteMeasure P] [IsFiniteMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : Measurable h) (hh' : Measurable h')
    (hlaw : P.map h = P'.map h') {S : Set DistC} (hS : LQGMetric.UMeasurableSet S) :
    P (h ⁻¹' S) = P' (h' ⁻¹' S) := by
  rw [prob_preimage_eq_law_of_um P hh hS, prob_preimage_eq_law_of_um P' hh' hS, hlaw]

 
theorem prob_preimage_eq_of_normalized {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (hh' : IsNormalizedWholePlaneGFF h' P') {S : Set DistC}
    (hS : LQGMetric.UMeasurableSet S) :
    P (h ⁻¹' S) = P' (h' ⁻¹' S) :=
  prob_preimage_eq_of_map_eq P P' hh.1.measurable hh'.1.measurable
    (map_eq_of_candidate_normalized hh hh') hS

 
theorem HEvent_prob_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (hh' : IsNormalizedWholePlaneGFF h' P') (D D' : DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D') (ξ Q : ℝ) (r : Ioi (0 : ℝ))
    (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) :
    P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q r a C θ (h ω)} =
      P' {ω | OptimalConstants.Ratios.HEvent D D' ξ Q r a C θ (h' ω)} :=
  prob_preimage_eq_of_normalized P P' hh hh' (HEvent_um D D' hD hD' ξ Q r a C θ)

 
theorem HtildeEvent_prob_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (hh' : IsNormalizedWholePlaneGFF h' P') (D D' : DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D') (ξ Q : ℝ) (r : Ioi (0 : ℝ))
    (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) :
    P {ω | OptimalConstants.Ratios.HtildeEvent D D' ξ Q r a C θ (h ω)} =
      P' {ω | OptimalConstants.Ratios.HtildeEvent D D' ξ Q r a C θ (h' ω)} :=
  prob_preimage_eq_of_normalized P P' hh hh' (HtildeEvent_um D D' hD hD' ξ Q r a C θ)

 
theorem GEvent_prob_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (hh' : IsNormalizedWholePlaneGFF h' P') (D D' : DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D') (r κ C : Ioi (0 : ℝ)) :
    P {ω | OptimalConstants.Ratios.G (D (h ω)) (D' (h ω)) r κ C} =
      P' {ω | OptimalConstants.Ratios.G (D (h' ω)) (D' (h' ω)) r κ C} :=
  prob_preimage_eq_of_normalized P P' hh hh' (TwoScale.S36Events.GEvent_um D D' hD hD' r κ C)

 
theorem GtildeEvent_prob_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (hh' : IsNormalizedWholePlaneGFF h' P') (D D' : DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D') (r κ C : Ioi (0 : ℝ)) :
    P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) r κ C} =
      P' {ω | OptimalConstants.Ratios.Gtilde (D (h' ω)) (D' (h' ω)) r κ C} :=
  prob_preimage_eq_of_normalized P P' hh hh' (TwoScale.S36Events.GtildeEvent_um D D' hD hD' r κ C)

 
theorem AttainedEvent_prob_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (hh' : IsNormalizedWholePlaneGFF h' P') (D D' : DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D') (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (C θ : Ioi (0 : ℝ)) (Cminus Cplus : ℝ) :
    P (h ⁻¹' TwoScale.S36Events.AttainedEvent D D' ξ Q z r q a K C θ Cminus Cplus) =
      P' (h' ⁻¹' TwoScale.S36Events.AttainedEvent D D' ξ Q z r q a K C θ Cminus Cplus) :=
  prob_preimage_eq_of_normalized P P' hh hh'
    (AttainedEvent_um D D' hD hD' ξ Q z r q a K C θ Cminus Cplus)

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
