/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeREtaVersions

/-! # GW4: mean uniqueness on an event of equal physical sets -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart Sec7.R5Enl Supp8.RelSafe

/-- The physical record determines the same mean on an event where the
two retained sets agree. Neither set has to be physical-record measurable. -/
theorem ae_localSetMean_eq_on {Ω : Type*} {𝓕 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν]
    (h𝓕 : 𝓕 ≤ mΩ) (hNull : Ito.nullSets ν ≤ 𝓕)
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X ν)
    {A B : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A)
    (hBm : Measurable[mΩ, hittingSigma] B)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hAl : IsHistoryAvoidanceLocal 𝓕 A X ν)
    (hBl : IsHistoryAvoidanceLocal 𝓕 B X ν)
    {G : Set Ω} (hG : MeasurableSet[𝓕] G)
    (hEq : ∀ᵐ ω ∂ν, ω ∈ G → A ω = B ω)
    {gA gB : Ω → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean A X ν gA) (hgB : IsLocalSetMean B X ν gB) :
    ∀ᵐ ω ∂ν, ω ∈ G → gA ω = gB ω := by
  obtain ⟨a, ham, -, hak⟩ := Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal
    hX hAm h𝓕 hAl (Eventually.of_forall hAc)
  obtain ⟨b, hbm, -, hbk⟩ := Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal
    hX hBm h𝓕 hBl (Eventually.of_forall hBc)
  let 𝓜A := germSigma A X ⊔ 𝓕
  let 𝓜B := germSigma B X ⊔ 𝓕
  let : MeasurableSpace Ω := mΩ
  have hmA : 𝓜A ≤ mΩ := sup_le (germSigma_le hAm hX.measurable) h𝓕
  have hmB : 𝓜B ≤ mΩ := sup_le (germSigma_le hBm hX.measurable) h𝓕
  have hga : gA =ᵐ[ν] a := ae_eq_of_isLocalSetMean_of_retained hX.measurable
    hgA le_sup_left hmA ham hak
  have hgb : gB =ᵐ[ν] b := ae_eq_of_isLocalSetMean_of_retained hX.measurable
    hgB le_sup_left hmB hbm hbk
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hEq)
  have hNae : ∀ᵐ ω ∂ν, ω ∉ N := by
    apply ae_iff.2
    have he : {ω | ¬ ω ∉ N} = N := Set.ext fun _ => not_not
    rw [he]
    exact hN0
  have hNF : MeasurableSet[𝓕] N := measurableSet_of_null hNull hNm hN0
  let D := Nᶜ ∩ G
  have hDF : MeasurableSet[𝓕] D := hNF.compl.inter hG
  have hDA : MeasurableSet[𝓜A] D := (le_sup_right : 𝓕 ≤ 𝓜A) _ hDF
  have hDB : MeasurableSet[𝓜B] D := (le_sup_right : 𝓕 ≤ 𝓜B) _ hDF
  have hEqD : ∀ ω ∈ D, A ω = B ω := by
    intro ω hω
    by_contra hn
    exact hω.1 (hNsub (show ¬ (ω ∈ G → A ω = B ω) from fun h => hn (h hω.2)))
  have he := ae_eq_of_isCondZeroBoundaryGFF_of_trace hmA hmB hDA
    (measurableSet_inter_germSigma_sup_iff hEqD rfl hDA hDB)
    hX.measurable (ham.mono le_sup_left le_rfl) (hbm.mono le_sup_left le_rfl) hak hbk
    (Eventually.of_forall fun ω hω => congrArg (fun S : Set ℂ => H \ S) (hEqD ω hω))
  filter_upwards [hga, hgb, hNae, he] with ω hgaω hgbω hNω heω hω
  exact hgaω.trans ((heω ⟨hNω, hω⟩).trans hgbω.symm)

end InteractingSLE.Theorem14.GW4Fix
