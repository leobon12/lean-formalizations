import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.ShiftedNormalization
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.NormalizedRNWindow




 






set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem fV2_probability_window_of_raw_measurable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ))
    (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z)
    (hraw_measurable : MeasurableSet
      {g : DistC | EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z g}) :
    ENNReal.ofReal ((par.Crn⁻¹) ^ Z.card) *
      P {ω | EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z (h ω)} ≤
      P (EndSaving.FiniteEvents.ShiftedFV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z) ∧
    P (EndSaving.FiniteEvents.ShiftedFV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z) ≤
      ENNReal.ofReal (par.Crn ^ Z.card) *
        P {ω | EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
          r b q K₁ K₂ obj Z (h ω)} := by
  let E : Set DistC :=
    {g | EndSaving.NormalizedEvent.NormalizedFV2 P h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z g}
  have hwindow := normalized_fV2_probability_window_of_raw_measurable
    P h hh D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z
    hconfig hraw_measurable
  have hEq0 : P (sampleEvent h E) =
      P {ω | EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z (h ω)} := by
    apply measure_congr
    filter_upwards [EndSaving.NormalizedEvent.normalizedFV2_ae_iff_raw P h hh
      D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z] with ω hω
    exact propext hω
  have hEqShift :
      P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
        (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z))) E) =
      P (EndSaving.FiniteEvents.ShiftedFV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z) := by
    apply measure_congr
    filter_upwards [normalizedFV2_shifted_ae_iff_raw
      P h hh D D' ξ Q cMid cPlus hD hD' par pbar
      r b q K₁ K₂ obj Z] with ω hω
    exact propext hω
  simpa only [E, hEq0, hEqShift] using hwindow

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
