/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfMeanNested

/-! # Passing stopped union mean identities through a countable live cover -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Sf

open LocalSets WholeField

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} {𝓜 : ℕ → MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Any property of every stopped union mean passes to the given local-set
 mean on a countable cover. The common enlargement is the physical union on
 the live event and the whole half plane elsewhere. Only the stopped marks
 need be field-determined. -/
theorem ae_property_of_marked_stopped_cover
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hℋ : ℋ ≤ mΩ) (hN : Ito.nullSets P ≤ ℋ)
    {B C : Ω → Set ℂ} (hB : Measurable[mΩ, hittingSigma] B)
    (hC : Measurable[ℋ, hittingSigma] C)
    (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hCc : ∀ᵐ ω ∂P, C ω ⊆ H ∧ IsOpen (H \ C ω))
    (hlB : IsHistoryAvoidanceLocal ℋ B h P) (hBC : ∀ᵐ ω ∂P, B ω ⊆ C ω)
    {E : Set Ω} (hE : MeasurableSet[ℋ] E)
    (heB : ∀ᵐ ω ∂P, ω ∈ E → B ω = C ω)
    {A : ℕ → Ω → Set ℂ} (h𝓜 : ∀ n, 𝓜 n ≤ mΩ) (h𝓜N : ∀ n, Ito.nullSets P ≤ 𝓜 n)
    (h𝓜d : ∀ n, 𝓜 n ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hA : ∀ n, Measurable[𝓜 n, hittingSigma] (A n))
    (hAc : ∀ n, ∀ᵐ ω ∂P, A n ω ⊆ H ∧ IsOpen (H \ A n ω))
    (hlA : ∀ n, IsHistoryAvoidanceLocal (𝓜 n) (A n) h P)
    (hAC : ∀ n, ∀ᵐ ω ∂P, A n ω ⊆ C ω)
    {En : ℕ → Set Ω} (hEn : ∀ n, MeasurableSet[𝓜 n] (En n))
    (heA : ∀ n, ∀ᵐ ω ∂P, ω ∈ En n → A n ω = C ω)
    (hcover : ∀ᵐ ω ∂P, ω ∈ E → ∃ n, ω ∈ En n)
    {Q : Ω → DistOn upperHalfPlaneOpens → Prop}
    (hQ : ∀ n (g : Ω → DistOn upperHalfPlaneOpens), IsLocalSetMean (A n) h P g →
      ∀ᵐ ω ∂P, ω ∈ En n → Q ω (g ω))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean B h P g) :
    ∀ᵐ ω ∂P, ω ∈ E → Q ω (g ω) := by
  have hCm := hC.mono hℋ le_rfl
  have hlC := Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set hlB hC hBC
  have hlClocal : IsLocalSet C h P :=
    ((isLocalSet_tfae hh hCm hCc).out 4 1).2 hlC.isAvoidanceLocal
  obtain ⟨gC, hgC⟩ := IsLocalSet.exists_isLocalSetMean hh hCm hlClocal
  have heBC := ae_mean_eq_on_marked_event hh hℋ hN hB hCm hBc hCc hlB hlC hE heB hg hgC
  have hstep : ∀ n, ∀ᵐ ω ∂P, ω ∈ En n → Q ω (gC ω) := by
    intro n
    have hl : IsLocalSet (A n) h P :=
      ((isLocalSet_tfae hh ((hA n).mono (h𝓜 n) le_rfl) (hAc n)).out 4 1).2 (hlA n).isAvoidanceLocal
    obtain ⟨gA, hgA⟩ := IsLocalSet.exists_isLocalSetMean hh ((hA n).mono (h𝓜 n) le_rfl) hl
    have he := ae_mean_eq_on_nested_determined hh (h𝓜 n) hℋ (h𝓜N n) (h𝓜d n)
      (hA n) hC (hAc n) hCc (hlA n) hlC (hAC n) (hEn n) (heA n) hgA hgC
    filter_upwards [he, hQ n gA hgA] with ω heω hQω hω
    rw [← heω hω]
    exact hQω hω
  filter_upwards [heBC, hcover, ae_all_iff.2 hstep] with ω heω hcω hQω hω
  obtain ⟨n, hn⟩ := hcω hω
  rw [heω hω]
  exact hQω n hn

end InteractingSLE.Theorem14.GW2Sf
