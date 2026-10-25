import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.NormalizedBorelProxy




set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem raw_fV2_borel_proxy
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
    : ∃ B : Set DistC,
      MeasurableSet B ∧
      (∀ g : DistC, ∀ c : ℝ,
        g ∈ B ↔ LQGMetric.addConst g c ∈ B) ∧
      (∀ g ∈ B, ∀ i ∈ Z, g ∈ (obj i).E) ∧
      (∀ᵐ g ∂(P.map h),
        (EndSaving.NormalizedEvent.NormalizedFV2 P h D D' ξ Q cMid cPlus par pbar
          r b q K₁ K₂ obj Z g) = (g ∈ B)) ∧
      (∀ᵐ g ∂(P.map (fun ω => LQGMetric.addFun (h ω)
          (LQGMetric.testCont
            (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z)))),
        (EndSaving.NormalizedEvent.NormalizedFV2 P h D D' ξ Q cMid cPlus par pbar
          r b q K₁ K₂ obj Z g) = (g ∈ B)) := by
  let Eraw : Set DistC :=
    {g | EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z g}
  let E : Set DistC :=
    {g | EndSaving.NormalizedEvent.NormalizedFV2 P h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z g}
  let φ := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z
  let shift : Ω → DistC :=
    fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)
  have hmshift : Measurable shift :=
    (LQGMetric.measurable_addFun_left (LQGMetric.testCont φ)).comp hh.1.measurable
  let μ₀ : Measure DistC := P.map h
  let μ₁ : Measure DistC := P.map shift
  have : IsFiniteMeasure μ₀ := inferInstance
  have : IsFiniteMeasure μ₁ := inferInstance
  have hraw : NullMeasurableSet Eraw μ₀ :=
    Measurability.FiniteFieldEvents.rawFV2_nullMeasurable P h hh D D' hD hD'
      cMid cPlus par pbar r b q K₁ K₂ hK₁ hK₂ obj Z
  have hfix : μ₀.map EndSaving.NormalizedEvent.normalizedField = μ₀ :=
    normalized_law_map_eq P h hh
  have hAC : μ₁.map EndSaving.NormalizedEvent.normalizedField ≪ μ₀ :=
    normalized_shift_law_ac P h hh φ
  have hFm : ∀ i ∈ Z, MeasurableSet (obj i).E := by
    intro i _; exact (obj i).E_measurable
  have hFc : ∀ i ∈ Z, ∀ g : DistC, ∀ c : ℝ,
      g ∈ (obj i).E ↔ LQGMetric.addConst g c ∈ (obj i).E := by
    intro i _ g c; exact (obj i).E_constant g c
  have hEF : ∀ g : DistC, EndSaving.NormalizedEvent.normalizedField g ∈ Eraw →
      ∀ i ∈ Z, g ∈ (obj i).E := by
    intro g hg i hi
    have hlocal : EndSaving.NormalizedEvent.normalizedField g ∈ (obj i).E := by
      rcases hg.1 with ⟨_, _, _, _, _, hloc, _, _, _, _⟩
      exact (hloc i hi).1
    exact ((obj i).E_constant g (-(EndSaving.NormalizedEvent.unitNorm g))).2 hlocal
  obtain ⟨B, hBm, hBc, hBg, hEq₀, hEq₁⟩ :=
    normalized_borel_proxy_two_laws μ₀ μ₁ Eraw hraw
      EndSaving.NormalizedEvent.normalizedField EndSaving.NormalizedEvent.measurable_normalizedField
      EndSaving.NormalizedEvent.normalizedField_addConst hfix hAC
      Z (fun i => (obj i).E) hFm hFc hEF
  exact ⟨B, hBm, hBc, hBg, hEq₀, hEq₁⟩

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
