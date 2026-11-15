/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWRestartFields
import InteractingSLE.Spec.Sec5.Aux61GWordCapture

/-! # Source contact endpoints and countable capture from the actual geometry -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61FibData Aux61GInst Aux61Restart
open WangWu (negInv)

/-- The original-target normalization already proves the physical scale
formula; that formula is not a separate assumption for source capture. -/
theorem SourceChartGeometry.scale {W : ℝ → ℝ} {η : ℝ → ℂ}
    {K : Set ℂ} {r : ℝ≥0} {c : Chart} (hg : SourceChartGeometry W η K r c)
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η)
    (harc : WangWu.IsProperArc η) (hc : c.IsConformal) :
    ∃ a ξ : ℝ, 0 < a ∧ EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull c.dom) (stripRightRetarget z) - ξ)) c.dom := by
  have hown : (c.dom : Set ℂ) ⊆ H \ fwdHull W r := by
    rw [WangWu.fwdHull_eq_image_Ioc hη harc r.coe_nonneg]
    intro z hz
    exact ⟨(hg.retained hz).1, fun hzP => (hg.retained hz).2
      (Or.inr (image_mono Ioc_subset_Icc_self hzP))⟩
  exact exists_original_target_chart_scale (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW r.coe_nonneg)
    (isHPHull_fwdHull hW r.coe_nonneg).2.2.2 (fun _ hz => hz.1) c.dom.isOpen hg.simply hown
    (isConformalBijection_fwdMapInv hW hW0 r.coe_nonneg)
    (harc.mem_H r (NNReal.coe_pos.2 hg.start_pos))
    (hη.tendsto_fwdMapInv_tip hW hW0 r.coe_nonneg) hg.collar hg.target
    (Sec7.Aux2728Pocket.isConformalBijection_fwd hc) hg.current hg.infty

/-- The selected access at an actual finite first contact has a nonzero
real chart endpoint. Both the physical scale and non-target contact are
proved from the source geometry and proper physical flow line. -/
theorem exists_real_source_accessEndpoint {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E) (hpos : 0 < T x) (hfin : T x < ⊤)
    {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ≥0}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (harc : WangWu.IsProperArc η)
    {Wcf : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hβ : IsLoewnerTrace Wcf β)
    {b : ℂ} (hb : b ∈ retainedDomain (negInv '' fwdHull Wcf s) η r)
    (hdom : ((c x).dom : Set ℂ) = restartComponent (negInv '' fwdHull Wcf s) η r b)
    (hg : SourceChartGeometry W η (negInv '' fwdHull Wcf s) r (c x))
    (hfirst : T x = hitTime ρ (fun _ => (H \ negInv '' fwdHull Wcf s)ᶜ) x)
    (hversion : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = η (r + (u : ℝ))) :
    ∃ y : ℝ, y ≠ 0 ∧
      Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ)) := by
  obtain ⟨y, hy, _, hlim⟩ := Aux61GNext.exists_real_glued_accessEndpoint hs hx hpos hfin
    hs0 hβ (harc.cont.mono Icc_subset_Ici_self)
    (fun t ht => by
      rcases ht.1.eq_or_lt with he | he
      · rw [← he, harc.zero]
        exact zero_mem_Hbar
      · exact H_subset_Hbar (harc.mem_H t he))
    hb hdom hg.simply hg.target (hg.scale hW hW0 hη harc (hs.conf x hx)) hfirst
    (restart_contact_ne_target (hs.contρ x hx) harc hpos hfin hversion)
  exact ⟨y, hy, hlim⟩

/-- Every actual finite source contact is captured by the fixed countable
buffered windows. The choice of a capturing index is made only here,
after the physical path; no history measurability of that choice is asserted. -/
theorem exists_countable_capture_of_source {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E) (hpos : 0 < T x) (hfin : T x < ⊤)
    {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ≥0}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (harc : WangWu.IsProperArc η)
    {Wcf : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hβ : IsLoewnerTrace Wcf β)
    {b : ℂ} (hb : b ∈ retainedDomain (negInv '' fwdHull Wcf s) η r)
    (hdom : ((c x).dom : Set ℂ) = restartComponent (negInv '' fwdHull Wcf s) η r b)
    (hg : SourceChartGeometry W η (negInv '' fwdHull Wcf s) r (c x))
    (hfirst : T x = hitTime ρ (fun _ => (H \ negInv '' fwdHull Wcf s)ᶜ) x)
    (hversion : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = η (r + (u : ℝ))) :
    ∃ y : ℝ, y ≠ 0 ∧ Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ)) ∧
      ∀ O : Set ℝ, IsOpen O → 0 ∈ O → y ∈ O →
        ∃ i : Aux61GWord.SeedWindowIndex, IsOpen (Aux61GWord.bufferedWindow i) ∧
          (0 : ℂ) ∈ Aux61GWord.bufferedWindow i ∧
          IsCompact (closure (Aux61GWord.outerBuffer i)) ∧
          (∀ z ∈ closure (Aux61GWord.outerBuffer i), z.im = 0 → z.re ∈ O) ∧
          (∀ u : ℝ≥0, (u : ℝ≥0∞) < T x → inPath E c ρ T x u ∈ Aux61GWord.bufferedWindow i) ∧
          (y : ℂ) ∉ Aux61GWord.bufferedWindow i ∧
          Aux61FibData.exitTime E c ρ T (Aux61GWord.bufferedWindow i) x = T x := by
  obtain ⟨y, hy, hlim⟩ := exists_real_source_accessEndpoint hs hx hpos hfin
    hW hW0 hη harc hs0 hβ hb hdom hg hfirst hversion
  refine ⟨y, hy, hlim, fun O hO hO0 hOy => ?_⟩
  obtain ⟨i, _, hVo, hV0, _, hUc, hUr, hin, hout, heq⟩ :=
    Aux61GWord.exists_countable_capture_of_access_limit hs hx hpos hfin hy hlim hO hO0 hOy
  exact ⟨i, hVo, hV0, hUc, hUr, hin, hout, heq⟩

/-- The countable capturing window can have an arbitrarily small positive
seed gap. Shrinking only that gap preserves the interior slit, the omitted
real endpoint and the outer buffer. It therefore fits the same free collar
used by selected-access landing. -/
theorem exists_countable_capture_small_gap {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E) (hpos : 0 < T x) (hfin : T x < ⊤)
    {y : ℝ} (hy : y ≠ 0)
    (hlim : Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ)))
    {ε : ℝ} (hε : 0 < ε) {O : Set ℝ} (hO : IsOpen O) (hO0 : 0 ∈ O) (hOy : y ∈ O) :
    ∃ j : Aux61GWord.SeedWindowIndex,
      0 < ((j : Aux61GWord.WindowIndex).2.2 : ℝ) ∧ ((j : Aux61GWord.WindowIndex).2.2 : ℝ) < ε ∧
      IsOpen (Aux61GWord.bufferedWindow j) ∧ (0 : ℂ) ∈ Aux61GWord.bufferedWindow j ∧
      IsCompact (closure (Aux61GWord.outerBuffer j)) ∧
      (∀ z ∈ closure (Aux61GWord.outerBuffer j), z.im = 0 → z.re ∈ O) ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < T x → inPath E c ρ T x u ∈ Aux61GWord.bufferedWindow j) ∧
      (y : ℂ) ∉ Aux61GWord.bufferedWindow j ∧
      Aux61FibData.exitTime E c ρ T (Aux61GWord.bufferedWindow j) x = T x := by
  obtain ⟨i, hgap, _, _, _, hUc, hUr, hin, hout, _⟩ :=
    Aux61GWord.exists_countable_capture_of_access_limit hs hx hpos hfin hy hlim hO hO0 hOy
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_btwn (lt_min hε hgap)
  have hδgap : (δ : ℝ) ≤ ((i : Aux61GWord.WindowIndex).2.2 : ℝ) := (lt_min_iff.1 hδ).2.le
  let j : Aux61GWord.SeedWindowIndex :=
    ⟨((i : Aux61GWord.WindowIndex).1, (i : Aux61GWord.WindowIndex).2.1, δ), hδ0,
      zero_mem_seedExitWindow i.property.2.1.1 hδ0, i.property.2.2.1, i.property.2.2.2⟩
  have hsub : Aux61GWord.bufferedWindow j ⊆ Aux61GWord.bufferedWindow i := by
    intro z hz
    exact ⟨hz.1, fun hbad => hz.2 ⟨hbad.1, hδgap.trans hbad.2⟩⟩
  have hVo : IsOpen (Aux61GWord.bufferedWindow j) :=
    isOpen_seedExitWindow (Aux61GWord.isOpen_basisBuffer _) _
  have hbefore : ∀ u : ℝ≥0, (u : ℝ≥0∞) < T x →
      inPath E c ρ T x u ∈ Aux61GWord.bufferedWindow j := by
    intro u hu
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with hu0 | hu0
    · rw [← hu0, hs.inPath_zero hx hpos]
      exact j.property.2.1
    · refine ⟨(hin u hu).1, ?_⟩
      have hH : inPath E c ρ T x u ∈ H := by
        rw [hs.inPath_eq_fwd hx hu0 hu]
        exact (hs.conf x hx).fwd_mem (hs.inside x hx u hu0 hu)
      exact fun hbad => (ne_of_gt hH) hbad.1
  exact ⟨j, hδ0, (lt_min_iff.1 hδ).1, hVo, j.property.2.1, hUc, hUr,
    hbefore, fun hj => hout (hsub hj), Aux61GCont.exitTime_eq_of_before_mem hs hVo hx hbefore⟩

/-- A valid buffered window with gap below the free collar supplies both
window premises of `hasAccessLanding_glued_subwindow` automatically. -/
theorem bufferedWindow_fits_free_gap (i : Aux61GWord.SeedWindowIndex) {δ : ℝ}
    (hgap : ((i : Aux61GWord.WindowIndex).2.2 : ℝ) ≤ δ) :
    Bornology.IsBounded (Aux61GWord.outerBuffer i) ∧
      Aux61GWord.bufferedWindow i ⊆ seedExitWindow (Aux61GWord.outerBuffer i) δ := by
  refine ⟨i.property.2.2.2.isBounded.subset subset_closure, ?_⟩
  intro z hz
  exact ⟨i.property.2.2.1 (subset_closure hz.1), fun hbad => hz.2 ⟨hbad.1, hgap.trans hbad.2⟩⟩

end InteractingSLE.Sec5.Aux61SlitW
