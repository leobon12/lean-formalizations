/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaLocal
import InteractingSLE.Spec.Sec7.R5EnlLocal
import InteractingSLE.Spec.Sec7.Lemma725RefMarksGerm

/-!
# GW4: actual conditioned laws for earlier component references

The later canonical hull retains the earlier hull's germ. Its marked
Gaussian kernel and the earlier kernel therefore have nested records.
The proved physical chart and added-set measurability instantiate the
conditioned increment-law theorem. Every version of each canonical
local-set mean has this law; no reference-law hypothesis is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Supp8.RelSafe LocalSets WholeField Restart Sec7.R5Enl Sec7.PocketStopSide

/-- Component locality proves the actual reference increment law on the
current live event, for every version of the two canonical means. -/
theorem component_reference_increment_law {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
    {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hF : F.IsOk) (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    {s t : ℝ≥0} (hst : s ≤ t)
    (gOld gNow : Ω → DistOn upperHalfPlaneOpens)
    (hgOld : IsLocalSetMean (safeHull F Wd GT R V s) (centredField X u₀) ν gOld)
    (hgNow : IsLocalSetMean (safeHull F Wd GT R V t) (centredField X u₀) ν gNow) :
    HasOldChartIncrementLawOn ν {ω | lineClock F Wd GT V t ω < V ω}
      (componentLineChart F Wd GT R V s) (componentLineChart F Wd GT R V t) gOld gNow := by
  let 𝓕 := physFilt Frame.measurable_gw4Rec hWm ν
  let A : ℝ≥0 → Ω → Set ℂ := safeHull F Wd GT R V
  let Y : Ω → DistOn upperHalfPlaneOpens := centredField X u₀
  have hZero := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hloc.1
  have hAm : ∀ u, Measurable[mΩ, hittingSigma] (A u) := fun u =>
    (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver u).mono (𝓕.le u) le_rfl
  have hAr : ∀ u ω, A u ω ⊆ H ∧ IsOpen (H \ A u ω) := fun u ω =>
    ⟨safeHull_subset_H F Wd GT R V u ω, Frame.isOpen_H_diff_safeHull hver u ω⟩
  have hLoc : ∀ u, IsHistoryAvoidanceLocal (𝓕 u) (A u) Y ν := fun u =>
    component_safeHull_locality hF hGT hGTm hGTae hver hloc u
  have hAs : Measurable[𝓕 t, hittingSigma] (A s) :=
    (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver s).mono (𝓕.mono hst) le_rfl
  have hEnl := Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hZero (𝓕.le t)
    (hAm t) (hLoc t) hAs (fun ω =>
      inter_subset_left.trans (safeHull_mono hF hGT ω hst))
  have hInfoEnl : 𝓕 t ⊔ germSigma (A s) Y ≤ mΩ :=
    sup_le (𝓕.le t) (germSigma_le (hAm s) hZero.measurable)
  obtain ⟨g₀, hg₀, hHarm₀, hK₀⟩ := Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal
    hZero (hAm s) (𝓕.le s) (hLoc s) (Eventually.of_forall (hAr s))
  obtain ⟨g₁, hg₁, hHarm₁, hK₁⟩ := Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal
    hZero (hAm t) hInfoEnl hEnl (Eventually.of_forall (hAr t))
  let ℳ₀ := germSigma (A s) Y ⊔ 𝓕 s
  let ℳ₁ := germSigma (A t) Y ⊔ (𝓕 t ⊔ germSigma (A s) Y)
  let : MeasurableSpace Ω := mΩ
  have hℳ₁ : ℳ₁ ≤ mΩ := sup_le (germSigma_le (hAm t) hZero.measurable) hInfoEnl
  have hℳ₀ : ℳ₀ ≤ mΩ := sup_le (germSigma_le (hAm s) hZero.measurable) (𝓕.le s)
  have hInfo : ℳ₀ ≤ ℳ₁ := sup_le
    ((le_sup_right : germSigma (A s) Y ≤ 𝓕 t ⊔ germSigma (A s) Y).trans le_sup_right)
    ((𝓕.mono hst).trans ((le_sup_left : 𝓕 t ≤ 𝓕 t ⊔ germSigma (A s) Y).trans le_sup_right))
  let G : Set Ω := {ω | lineClock F Wd GT V s ω < V ω}
  have hGp : MeasurableSet[𝓕 s] G :=
    measurableSet_componentLine_live hF hGT hWm hGTm hGTae hver s
  have hG : MeasurableSet[ℳ₀] G := (le_sup_right : 𝓕 s ≤ ℳ₀) _ hGp
  have hOld : ∀ ω ∈ G, (componentLineChart F Wd GT R V s ω).IsConformal := by
    intro ω _
    have hW : Continuous (MartChar.wpath R ω) := (hver.1.1.2.1 ω).comp continuous_real_toNNReal
    have hW0 : MartChar.wpath R ω 0 = 0 := by
      simpa only [MartChar.wpath, Real.toNNReal_zero] using hver.1.1.2.2.1 ω
    exact Chart.isConformal_id.loewner hW hW0
      (lineClock F Wd GT V s ω).toNNReal.coe_nonneg
  have hDom : ∀ ω ∈ G, ((componentLineChart F Wd GT R V s ω).dom : Set ℂ) = H \ A s ω :=
    fun ω hω => (componentLineChart_domain (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)).trans
      (H_diff_safeHull_of_lt F Wd GT R V s ω hω).symm
  have hLaw : HasOldChartIncrementLawOn ν {ω | lineClock F Wd GT V t ω < V ω}
      (componentLineChart F Wd GT R V s) (componentLineChart F Wd GT R V t) g₀ g₁ := by
    apply hasOldChartIncrementLawOn_of_retained_kernels_noGerm
      (ℋ₀ := ℳ₀) (ℋ₁ := ℳ₁) hInfo hℳ₁ hG hOld
      (fun z => (le_sup_right : 𝓕 s ≤ ℳ₀) _ (hGp.inter
        (measurable_componentLineChart hF hGT hWm hGTm hGTae hver s z).2))
      (fun z => (measurable_componentLineChart_indicator hF hGT hWm hGTm hGTae hver s hGp z).mono
        le_sup_right le_rfl)
      (fun ω _ => (hAr t ω).2)
      (fun ω hω => by
        rw [hDom ω hω]
        exact fun z hz => ⟨hz.1, fun hzOld => hz.2 (safeHull_mono hF hGT ω hst hzOld)⟩)
      hZero.measurable
      (hg₀.mono ((le_sup_right : germSigma (A s) Y ≤ 𝓕 t ⊔ germSigma (A s) Y).trans le_sup_right) le_rfl)
      (hg₁.mono le_sup_left le_rfl)
      (hHarm₀.mono fun ω hω hωG => by rw [hDom ω hωG]; exact hω)
      (hHarm₁.mono fun _ hω _ => hω)
      (Eventually.of_forall fun ω hωG => (hDom ω hωG).symm)
      hK₀ hK₁
      ((measurable_componentLine_addedSet hF hGT hWm hGTm hGTae hver hst).mono
        ((le_sup_left : 𝓕 t ≤ 𝓕 t ⊔ germSigma (A s) Y).trans le_sup_right) le_rfl)
      (fun ω hω => (Frame.monotone_min_physClockG hF hGT (V := V) ω hst).trans_lt hω)
      (fun ω hω => (componentLineChart_domain (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)).trans
        (H_diff_safeHull_of_lt F Wd GT R V t ω hω).symm)
  have hEq₀ := ae_eq_of_isLocalSetMean_of_retained hZero.measurable hgOld
    (show germSigma (A s) Y ≤ ℳ₀ from le_sup_left) hℳ₀ hg₀ hK₀
  have hEq₁ := ae_eq_of_isLocalSetMean_of_retained hZero.measurable hgNow
    (show germSigma (A t) Y ≤ ℳ₁ from le_sup_left) hℳ₁ hg₁ hK₁
  apply hLaw.congr_on
  filter_upwards [hEq₀, hEq₁] with ω hω₀ hω₁ _
  exact ⟨rfl, rfl, hω₀.symm, hω₁.symm⟩

end InteractingSLE.Theorem14.GW4Fix
