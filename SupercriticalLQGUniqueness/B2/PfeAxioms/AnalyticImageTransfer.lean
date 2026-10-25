import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedLaw
import LQGMetric.Meas.UM

 







set_option autoImplicit false
noncomputable section

open MeasureTheory Set LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_field_property_of_standardBorel_coupling
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [StandardBorelSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistC) (h' : Ω' → DistC)
    (hh : Measurable h) (hh' : Measurable h')
    (hLaw : P.map h = P'.map h')
    (R : DistC → Prop)
    (hR : ∀ᵐ ω ∂P', R (h' ω)) :
    ∀ᵐ ω ∂P, R (h ω) := by
  have hBad : P' {ω | ¬ R (h' ω)} = 0 := ae_iff.mp hR
  obtain ⟨N, hNsub, hNm, hNzero⟩ :=
    exists_measurable_superset_of_null hBad
  let M : Set Ω' := Nᶜ
  have hMm : MeasurableSet M := hNm.compl
  have hMa : ∀ᵐ ω ∂P', ω ∈ M := by
    apply ae_iff.mpr
    simpa only [M, Set.mem_compl_iff, not_not, Set.ofPred_mem_eq] using hNzero
  have hMR : ∀ ω ∈ M, R (h' ω) := by
    intro ω hω
    by_contra hnot
    exact hω (hNsub hnot)
  let A : Set DistC := h' '' M
  have hAu : UMeasurableSet A := UMeasurableSet.image hh' hMm
  have hAn : NullMeasurableSet A (P'.map h') := hAu.nullMeasurableSet _
  obtain ⟨B, hBsub, hBm, hBae⟩ := hAn.exists_measurable_subset_ae_eq
  have hAa : ∀ᵐ g ∂(P'.map h'), g ∈ A := by
    apply ae_iff.mpr
    have hpre : P' (h' ⁻¹' Aᶜ) = 0 := by
      apply ae_iff.mp
      filter_upwards [hMa] with ω hω
      exact ⟨ω, hω, rfl⟩
    change (P'.map h') Aᶜ = 0
    rw [Measure.map_apply₀ hh'.aemeasurable hAn.compl]
    exact hpre
  have hBa : ∀ᵐ g ∂(P'.map h'), g ∈ B := by
    filter_upwards [hBae, hAa] with g hBA hgA
    exact hBA.mpr hgA
  rw [← hLaw] at hBa
  have hBsource : ∀ᵐ ω ∂P, h ω ∈ B :=
    ae_of_ae_map hh.aemeasurable hBa
  filter_upwards [hBsource] with ω hω
  obtain ⟨ω', hω'M, hω'eq⟩ := hBsub hω
  rw [← hω'eq]
  exact hMR ω' hω'M

end SupercriticalLQGUniqueness.B2.PfeAxioms
