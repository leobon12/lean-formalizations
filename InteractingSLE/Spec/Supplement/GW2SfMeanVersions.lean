/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlTrace
import InteractingSLE.Spec.Sec7.Lemma72CLocal
import InteractingSLE.Spec.Supplement.RelSafeCore

/-! # Comparing union means only on the event where the sets agree -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Sf

open LocalSets WholeField Sec7.R5Enl

variable {Ω : Type u} {ℋ ℋA ℋB : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Marked local versions have identical means on a common mark event where
 their sets agree. Null sets among the marks permit almost sure agreement. -/
theorem ae_mean_eq_on_marked_event
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hℋ : ℋ ≤ mΩ) (hNull : Ito.nullSets P ≤ ℋ)
    {A B : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A)
    (hBm : Measurable[mΩ, hittingSigma] B)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hlA : IsHistoryAvoidanceLocal ℋ A h P) (hlB : IsHistoryAvoidanceLocal ℋ B h P)
    {E : Set Ω} (hE : MeasurableSet[ℋ] E)
    (hEq : ∀ᵐ ω ∂P, ω ∈ E → A ω = B ω)
    {gA gB : Ω → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean A h P gA) (hgB : IsLocalSetMean B h P gB) :
    ∀ᵐ ω ∂P, ω ∈ E → gA ω = gB ω := by
  obtain ⟨a, ham, -, hak⟩ :=
    Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh hAm hℋ hlA hAc
  obtain ⟨b, hbm, -, hbk⟩ :=
    Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh hBm hℋ hlB hBc
  have hMA : germSigma A h ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hAm hh.measurable) hℋ
  have hMB : germSigma B h ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hBm hh.measurable) hℋ
  have hga := ae_eq_of_isLocalSetMean_of_retained hh.measurable hgA le_sup_left hMA ham hak
  have hgb := ae_eq_of_isLocalSetMean_of_retained hh.measurable hgB le_sup_left hMB hbm hbk
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hEq)
  have hNH : MeasurableSet[ℋ] N := Supp8.RelSafe.measurableSet_of_null hNull hNm hN0
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    apply ae_iff.2
    have he : {ω | ¬ ω ∉ N} = N := Set.ext fun _ => not_not
    rw [he]
    exact hN0
  let D : Set Ω := Nᶜ ∩ E
  have hDH : MeasurableSet[ℋ] D := hNH.compl.inter hE
  have hDA : MeasurableSet[germSigma A h ⊔ ℋ] D :=
    (le_sup_right : ℋ ≤ germSigma A h ⊔ ℋ) _ hDH
  have hDB : MeasurableSet[germSigma B h ⊔ ℋ] D :=
    (le_sup_right : ℋ ≤ germSigma B h ⊔ ℋ) _ hDH
  have heD : ∀ ω ∈ D, A ω = B ω := by
    intro ω hω
    by_contra hn
    exact hω.1 (hNsub (show ¬ (ω ∈ E → A ω = B ω) from fun he => hn (he hω.2)))
  have he := ae_eq_of_isCondZeroBoundaryGFF_of_trace hMA hMB hDA
    (measurableSet_inter_germSigma_sup_iff heD rfl hDA hDB)
    hh.measurable (ham.mono le_sup_left le_rfl) (hbm.mono le_sup_left le_rfl) hak hbk
    (Eventually.of_forall fun ω hω => congrArg (fun S : Set ℂ => H \ S) (heD ω hω))
  filter_upwards [hga, hgb, hNae, he] with ω ha hb hn heω hω
  exact ha.trans ((heω ⟨hn, hω⟩).trans hb.symm)

/-- A common measurable enlargement compares two marked-local means even
 when their marks are different. In applications it is the physical union
 on the comparison event and the whole half plane outside that event. -/
theorem ae_mean_eq_on_common_enlargement
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hℋA : ℋA ≤ mΩ) (hℋB : ℋB ≤ mΩ)
    (hNA : Ito.nullSets P ≤ ℋA) (hNB : Ito.nullSets P ≤ ℋB)
    {A B C : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A)
    (hBm : Measurable[mΩ, hittingSigma] B)
    (hCA : Measurable[ℋA, hittingSigma] C) (hCB : Measurable[ℋB, hittingSigma] C)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hCc : ∀ᵐ ω ∂P, C ω ⊆ H ∧ IsOpen (H \ C ω))
    (hlA : IsHistoryAvoidanceLocal ℋA A h P) (hlB : IsHistoryAvoidanceLocal ℋB B h P)
    (hAC : ∀ᵐ ω ∂P, A ω ⊆ C ω) (hBC : ∀ᵐ ω ∂P, B ω ⊆ C ω)
    {E : Set Ω} (hEA : MeasurableSet[ℋA] E) (hEB : MeasurableSet[ℋB] E)
    (hEqA : ∀ᵐ ω ∂P, ω ∈ E → A ω = C ω)
    (hEqB : ∀ᵐ ω ∂P, ω ∈ E → B ω = C ω)
    {gA gB : Ω → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean A h P gA) (hgB : IsLocalSetMean B h P gB) :
    ∀ᵐ ω ∂P, ω ∈ E → gA ω = gB ω := by
  have hCm := hCA.mono hℋA le_rfl
  have hlCA := Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set hlA hCA hAC
  have hlCB := Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set hlB hCB hBC
  have hlC : IsLocalSet C h P :=
    ((isLocalSet_tfae hh hCm hCc).out 4 1).2 hlCA.isAvoidanceLocal
  obtain ⟨gC, hgC⟩ := IsLocalSet.exists_isLocalSetMean hh hCm hlC
  have eA := ae_mean_eq_on_marked_event hh hℋA hNA hAm hCm hAc hCc hlA hlCA hEA hEqA hgA hgC
  have eB := ae_mean_eq_on_marked_event hh hℋB hNB hBm hCm hBc hCc hlB hlCB hEB hEqB hgB hgC
  filter_upwards [eA, eB] with ω ha hb hω
  exact (ha hω).trans (hb hω).symm

end InteractingSLE.Theorem14.GW2Sf
