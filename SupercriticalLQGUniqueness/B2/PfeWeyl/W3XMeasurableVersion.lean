import SupercriticalLQGUniqueness.B2.PfeAxioms.AnalyticImageTransfer
import SupercriticalLQGUniqueness.B2.LscTop.Limits
import Mathlib.MeasureTheory.Constructions.Polish.Basic

 











set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LQGMetric (UMeasurableSet)

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem exists_measurable_version_of_field_determined
    {S T Ω : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace T] [Nonempty T]
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (X : Ω → S) (hX : Measurable X) (hLaw : P.map X = μ)
    (F : S → T) (hFX : AEMeasurable (fun ω => F (X ω)) P) :
    ∃ G : S → T, Measurable G ∧ F =ᵐ[μ] G := by
  let Y : Ω → T := hFX.mk (fun ω => F (X ω))
  have hYm : Measurable Y := hFX.measurable_mk
  have hYeq : (fun ω => F (X ω)) =ᵐ[P] Y := hFX.ae_eq_mk
  have hBad : P {ω | F (X ω) ≠ Y ω} = 0 := ae_iff.mp hYeq
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null hBad
  let M : Set Ω := Nᶜ
  have hMm : MeasurableSet M := hNm.compl
  have hMa : ∀ᵐ ω ∂P, ω ∈ M := by
    apply ae_iff.mpr
    simpa only [M, Set.mem_compl_iff, not_not, Set.ofPred_mem_eq] using hNzero
  have hMF : ∀ ω ∈ M, F (X ω) = Y ω := by
    intro ω hω
    by_contra hnot
    exact hω (hNsub hnot)
  let A : Set S := X '' M
  have hAu : UMeasurableSet A := UMeasurableSet.image hX hMm
  have hAn' : NullMeasurableSet A (P.map X) := hAu.nullMeasurableSet _
  have hAn : NullMeasurableSet A μ := by
    simpa only [hLaw] using hAn'
  obtain ⟨B, hBsub, hBm, hBae⟩ := hAn.exists_measurable_subset_ae_eq
  have hAa : ∀ᵐ s ∂μ, s ∈ A := by
    apply ae_iff.mpr
    have hpre : P (X ⁻¹' Aᶜ) = 0 := by
      apply ae_iff.mp
      filter_upwards [hMa] with ω hω
      exact ⟨ω, hω, rfl⟩
    change μ Aᶜ = 0
    rw [← hLaw, Measure.map_apply₀ hX.aemeasurable hAn'.compl]
    exact hpre
  have hBa : ∀ᵐ s ∂μ, s ∈ B := by
    filter_upwards [hBae, hAa] with s hBA hsA
    exact hBA.mpr hsA
  let x : M → S := fun ω => X ω
  letI : StandardBorelSpace M := hMm.standardBorel
  have hxm : Measurable x := hX.comp measurable_subtype_coe
  have hcomp : Measurable (fun ω : M => F (x ω)) := by
    have heq : (fun ω : M => F (x ω)) = fun ω : M => Y ω := by
      funext ω
      exact hMF ω ω.property
    rw [heq]
    exact hYm.comp measurable_subtype_coe
  have hrestr : Measurable (domRestrict (range x) F) :=
    hxm.measurable_comp_iff_restrict.mp hcomp
  have hBA : B ⊆ range x := by
    intro s hs
    obtain ⟨ω, hω, rfl⟩ := hBsub hs
    exact ⟨⟨ω, hω⟩, rfl⟩
  have hinc : Measurable (fun s : B => (⟨s.1, hBA s.2⟩ : range x)) :=
    measurable_subtype_coe.subtype_mk
  have hFB : Measurable (fun s : B => F s.1) := hrestr.comp hinc
  obtain ⟨G, hG, hGB⟩ :=
    (MeasurableEmbedding.subtype_coe hBm).exists_measurable_extend hFB
      (fun _ => inferInstance)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hBa] with s hs
  exact (congrFun hGB ⟨s, hs⟩).symm

end SupercriticalLQGUniqueness.B2.PfeWeyl
