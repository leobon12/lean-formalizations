import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.FV2Proxy




set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 


theorem fV2_probability_window_of_raw_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (obj : ∀ i : ℤ × ℤ,
      ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ))
    (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z) :
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
  let φ := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z
  let shift : Ω → DistC :=
    fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)
  have hmshift : Measurable shift :=
    (LQGMetric.measurable_addFun_left (LQGMetric.testCont φ)).comp hh.1.measurable
  obtain ⟨B, hBm, hBc, hBg, hEq₀, hEq₁⟩ :=
    raw_fV2_borel_proxy P h hh D D' ξ Q cMid cPlus hD hD'
      par pbar r b q K₁ K₂ hK₁ hK₂ obj Z
  have hwindow := EndSaving.RadonNikodym.finiteBump_probability_window_of_objects
    P h hh D D' ξ Q cMid par pbar r Z
    (fun i => LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
    (fun i _ => obj i) hconfig.1 B hBm hBc hBg
  have hsum : (∑ i ∈ Z, if hi : i ∈ Z then (obj i).f else 0) =
      (∑ i ∈ Z, (obj i).f) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  have hae₀ : ∀ᵐ ω ∂P, (h ω ∈ E) = (h ω ∈ B) :=
    ae_of_ae_map hh.1.measurable.aemeasurable hEq₀
  have hEqRaw₀ : P (sampleEvent h B) =
      P {ω | EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z (h ω)} := by
    apply measure_congr
    filter_upwards [hae₀, EndSaving.NormalizedEvent.normalizedFV2_ae_iff_raw P h hh
      D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z] with ω he hr
    exact propext ((Iff.of_eq he).symm.trans hr)
  have hae₁ : ∀ᵐ ω ∂P, (shift ω ∈ E) = (shift ω ∈ B) :=
    ae_of_ae_map hmshift.aemeasurable hEq₁
  have hEqRaw₁ : P (sampleEvent shift B) =
      P (EndSaving.FiniteEvents.ShiftedFV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z) := by
    apply measure_congr
    filter_upwards [hae₁, EndSaving.Scaling.normalizedFV2_shifted_ae_iff_raw
      P h hh D D' ξ Q cMid cPlus hD hD' par pbar
      r b q K₁ K₂ obj Z] with ω he hr
    exact propext ((Iff.of_eq he).symm.trans hr)
  rw [← hEqRaw₁]
  simpa only [φ, shift, EndSaving.FiniteEvents.bumpSumV2, hsum, hEqRaw₀] using hwindow

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
