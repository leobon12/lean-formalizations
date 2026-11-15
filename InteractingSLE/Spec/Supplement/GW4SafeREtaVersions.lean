/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaReferences
import InteractingSLE.Spec.Sec7.R5EnlTrace

/-! # GW4: given means and canonical safe-hull means agree on live lines

Both sets have marked Gaussian kernels with the same physical marks.
On a live line their sets, germ records and domains agree. The committed
trace-of-records uniqueness theorem identifies the means on that event.
The physical marks contain all measurable null sets, so the almost sure
shape identity suffices without changing either version of the local set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Supp8.RelSafe LocalSets WholeField Restart Sec7.R5Enl

/-- Every given B-mean and every canonical safe-hull mean are the same
distribution on the actual live event of the physical line. -/
theorem ae_component_mean_eq_safeHull {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
    {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hF : F.IsOk) (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    (t : ℝ≥0) (g gSafe : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean (B t) (centredField X u₀) ν g)
    (hgSafe : IsLocalSetMean (safeHull F Wd GT R V t) (centredField X u₀) ν gSafe) :
    ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω → g ω = gSafe ω := by
  let A := safeHull F Wd GT R V t
  let Y := centredField X u₀
  let G : Set Ω := {ω | lineClock F Wd GT V t ω < V ω}
  have hZero := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hloc.1
  obtain ⟨-, hphys, hℋ, hBm, hBc, hBl, hShape⟩ := hloc
  have hAmH : Measurable[ℋ t, hittingSigma] A :=
    (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver t).mono (hphys t) le_rfl
  have hAm : Measurable[mΩ, hittingSigma] A := hAmH.mono (hℋ t) le_rfl
  have hAr : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω) := fun ω =>
    ⟨safeHull_subset_H F Wd GT R V t ω, Frame.isOpen_H_diff_safeHull hver t ω⟩
  have hBA : ∀ᵐ ω ∂ν, ω ∈ G → B t ω = A ω := by
    filter_upwards [hShape t] with ω hShapeω hω
    have hd : H \ B t ω = H \ A ω :=
      (hShapeω hω).trans (H_diff_safeHull_of_lt F Wd GT R V t ω hω).symm
    ext z
    have hzB := (hBc t ω).1
    have hzA := (hAr ω).1
    have hz := Set.ext_iff.1 hd z
    by_cases hzH : z ∈ H
    · simpa only [Set.mem_sdiff, hzH, true_and, not_iff_not] using hz
    · exact ⟨fun hz => (hzH (hzB hz)).elim, fun hz => (hzH (hzA hz)).elim⟩
  have hSub : ∀ᵐ ω ∂ν, B t ω ⊆ A ω := by
    filter_upwards [hBA] with ω hBAω
    by_cases hω : ω ∈ G
    · exact (hBAω hω).le
    · intro z hz
      simpa only [A, safeHull, show ¬ lineClock F Wd GT V t ω < V ω from hω,
        ↓reduceIte] using (hBc t ω).1 hz
  have hAl : IsHistoryAvoidanceLocal (ℋ t) A Y ν :=
    Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set (hBl t) hAmH hSub
  obtain ⟨b, hbm, -, hbk⟩ := Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal
    hZero (hBm t) (hℋ t) (hBl t) (Eventually.of_forall (hBc t))
  obtain ⟨a, ham, -, hak⟩ := Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal
    hZero hAm (hℋ t) hAl (Eventually.of_forall hAr)
  let ℳB := germSigma (B t) Y ⊔ ℋ t
  let ℳA := germSigma A Y ⊔ ℋ t
  let : MeasurableSpace Ω := mΩ
  have hℳB : ℳB ≤ mΩ := sup_le (germSigma_le (hBm t) hZero.measurable) (hℋ t)
  have hℳA : ℳA ≤ mΩ := sup_le (germSigma_le hAm hZero.measurable) (hℋ t)
  have hgb : g =ᵐ[ν] b := ae_eq_of_isLocalSetMean_of_retained hZero.measurable
    hg (show germSigma (B t) Y ≤ ℳB from le_sup_left) hℳB hbm hbk
  have hga : gSafe =ᵐ[ν] a := ae_eq_of_isLocalSetMean_of_retained hZero.measurable
    hgSafe (show germSigma A Y ≤ ℳA from le_sup_left) hℳA ham hak
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hBA)
  have hNae : ∀ᵐ ω ∂ν, ω ∉ N := by
    apply ae_iff.2
    have he : {ω | ¬ ω ∉ N} = N := Set.ext fun _ => not_not
    rw [he]
    exact hN0
  have hNull : Ito.nullSets ν ≤ ℋ t :=
    (nullSets_le_physFilt Frame.measurable_gw4Rec hWm ν t).trans (hphys t)
  have hNH : MeasurableSet[ℋ t] N := measurableSet_of_null hNull hNm hN0
  have hGH : MeasurableSet[ℋ t] G := hphys t _
    (measurableSet_componentLine_live hF hGT hWm hGTm hGTae hver t)
  let D : Set Ω := Nᶜ ∩ G
  have hDH : MeasurableSet[ℋ t] D := hNH.compl.inter hGH
  have hDB : MeasurableSet[ℳB] D := (le_sup_right : ℋ t ≤ ℳB) _ hDH
  have hDA : MeasurableSet[ℳA] D := (le_sup_right : ℋ t ≤ ℳA) _ hDH
  have hEqD : ∀ ω ∈ D, B t ω = A ω := by
    intro ω hω
    by_contra hn
    exact hω.1 (hNsub (show ¬ (ω ∈ G → B t ω = A ω) from fun h => hn (h hω.2)))
  have hEq := ae_eq_of_isCondZeroBoundaryGFF_of_trace hℳB hℳA hDB
    (measurableSet_inter_germSigma_sup_iff hEqD rfl hDB hDA)
    hZero.measurable (hbm.mono le_sup_left le_rfl) (ham.mono le_sup_left le_rfl) hbk hak
    (Eventually.of_forall fun ω hω => congrArg (fun S : Set ℂ => H \ S) (hEqD ω hω))
  filter_upwards [hgb, hga, hNae, hEq] with ω hgbω hgaω hNω hEqω hLive
  exact hgbω.trans ((hEqω ⟨hNω, hLive⟩).trans hgaω.symm)

end InteractingSLE.Theorem14.GW4Fix
