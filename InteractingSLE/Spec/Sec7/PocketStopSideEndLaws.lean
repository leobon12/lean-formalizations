/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideCloseLaws
import InteractingSLE.Spec.Sec7.Lemma725RefMarksPocket

/-!
# Exterior marks in the side comparison

PROVE-STRIPSYS38. REF6's smaller-germ theorem applies after the pocket exterior
has been filled. This supplies the stage union laws from the raw union laws,
including the unions with ordinary reference hulls. The raw walls law retains
its original marks, as required by amended R68. No counterflow determination
is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketStopField
  PocketUnionPt PocketCoupling

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- A smaller, history-measurable set's germ may be retained in the filled
pocket union law. Only its inclusion on the live event is needed. -/
theorem pocketStopUnionLaw_sup_germSigma {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F E₀ : Ω → Set ℂ} {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hE₀ : Measurable[locPrefixSigma 𝓦 A γ q, hittingSigma] E₀)
    (hsub : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      E₀ ω ∩ H ⊆ extHullSet (C ω) (F ω))
    (hU : PocketStopUnionLaw 𝓦 P A γ C F h₀ q) :
    PocketStopUnionLaw (𝓦 ⊔ germSigma E₀ h₀) P A γ C F h₀ q := by
  obtain ⟨E, hEm, hEloc, hEq⟩ := hU
  have hL := measurableSet_live (𝓦 := 𝓦) A γ q
  have hloc := isHistoryAvoidanceLocal_liveExt hL hEloc hEq
  have hm := measurable_liveExt (hpre _ hL) hEm hEq
  have hsub' : ∀ ω, E₀ ω ∩ H ⊆ liveExt A γ C F q ω := by
    intro ω z hz
    by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
    · rw [liveExt_of_live hl]
      exact hsub ω hl.1 hl.2 hz
    · rw [liveExt_of_not_live hl]
      exact hz.2
  have hME := Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma
    hh₀ hpre hm hloc hE₀ hsub'
  refine ⟨liveExt A γ C F q, hm, ?_, fun ω hω hq => liveExt_of_live ⟨hω, hq⟩⟩
  rw [locPrefixSigma_sup_info]
  exact hME

/-- A germ-measurable exterior projection can be added to the stage information
without assuming a new union law for that projection. -/
theorem pocketStopUnionLaw_sup_exteriorField {h₀ hB : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F E₀ : Ω → Set ℂ} {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hE₀ : Measurable[locPrefixSigma 𝓦 A γ q, hittingSigma] E₀)
    (hsub : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      E₀ ω ∩ H ⊆ extHullSet (C ω) (F ω))
    (hhB : Measurable[germSigma E₀ h₀] hB)
    (hU : PocketStopUnionLaw 𝓦 P A γ C F h₀ q) :
    PocketStopUnionLaw (𝓦 ⊔ MeasurableSpace.comap hB inferInstance) P A γ C F h₀ q := by
  obtain ⟨E, hEm, hEloc, hEq⟩ := pocketStopUnionLaw_sup_germSigma hh₀ hpre hE₀ hsub hU
  refine ⟨E, hEm, ?_, hEq⟩
  have hle : locPrefixSigma (𝓦 ⊔ MeasurableSpace.comap hB inferInstance) A γ q ≤
      locPrefixSigma (𝓦 ⊔ germSigma E₀ h₀) A γ q := by
    unfold locPrefixSigma
    exact sup_le_sup (sup_le_sup_left hhB.comap_le 𝓦) le_rfl
  exact fun U G hUH hG hd M hM => hEloc U G hUH hG hd M (hle M hM)

/-- Fill a walls law first and then add the exterior projection. This order also
applies to the maximum-reference walls laws of `CloseMax`. -/
theorem pocketStopUnionLaw_sup_exteriorField_of_wallsLaw
    {h₀ hB : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C Γ F E₀ : Ω → Set ℂ} {q : ℝ≥0}
    (h𝓦 : 𝓦 ≤ mΩ) (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hΓC : ∀ ω ∈ A, Disjoint (H ∩ Γ ω) (C ω))
    (hfr : ∀ ω ∈ A, frontier (C ω) ∩ H ⊆ Γ ω)
    (hE₀ : Measurable[locPrefixSigma 𝓦 A γ q, hittingSigma] E₀)
    (hsub : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      E₀ ω ∩ H ⊆ extHullSet (C ω) (F ω))
    (hhB : Measurable[germSigma E₀ h₀] hB)
    (hW : PocketStopWallsLaw 𝓦 P A γ Γ F h₀ q) :
    PocketStopUnionLaw (𝓦 ⊔ MeasurableSpace.comap hB inferInstance) P A γ C F h₀ q :=
  pocketStopUnionLaw_sup_exteriorField hh₀ hpre hE₀ hsub hhB
    (pocketStopUnionLaw_of_wallsLaw h𝓦 hpre hCm hCo hΓC hfr hW)

/-- REF6's actual exterior `extA A C` is contained in every filled comparison
union. Thus the same exterior projection can mark every reference law, with
no separate containment or enlarged-law input. -/
theorem pocketStopUnionLaw_sup_pocketExterior {h₀ hB : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F : Ω → Set ℂ} {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ) (hA : MeasurableSet[𝓦] A)
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    (hhB : Measurable[germSigma (Lemma725RefMarks.extA A C) h₀] hB)
    (hU : PocketStopUnionLaw 𝓦 P A γ C F h₀ q) :
    PocketStopUnionLaw (𝓦 ⊔ MeasurableSpace.comap hB inferInstance) P A γ C F h₀ q := by
  apply pocketStopUnionLaw_sup_exteriorField hh₀ hpre
    ((Lemma725RefMarks.measurable_extA hA hCin).mono le_sup_left le_rfl) ?_ hhB hU
  intro ω hω _ z hz
  rw [Lemma725RefMarks.extA_of_mem hω] at hz
  exact ⟨hz.1.1, Or.inl hz.1.2⟩

end InteractingSLE.Sec7.PocketStopSide
