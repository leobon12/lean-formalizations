/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBMeas
import InteractingSLE.Spec.Sec7.PocketTraversalErase

/-!
# The mapped continuous curve and its local drivers

Boundary values of the relative chart map real points to real points. Hence
adjoining these values preserves the filling identity already proved by GB6's
fixed-hull restriction. A time change of a compact open prefix is a driven
curve without a positive-time interior-point hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex MeasureTheory Bornology
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Supp8.GB6.CoordB

open Q3Rel (invHull)
open Sec7.Lemma71C (capClock)

/-- Inversion sends a bounded hull away from the origin. -/
theorem zero_notMem_closure_invHull {U : ℝ → ℝ} (hU : Continuous U) {s : ℝ} (hs : 0 ≤ s) :
    (0 : ℂ) ∉ closure (invHull U s) := by
  obtain ⟨M, hM⟩ := (isBounded_fwdHull hU s).subset_closedBall 0
  intro h0
  obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.1 h0 (1 / (|M| + 1)) (by positivity)
  obtain ⟨z, hz, rfl⟩ := hw
  have hz0 : z ≠ 0 := ne_zero_of_mem_H ((isHPHull_fwdHull hU hs).1 hz)
  have hzM : ‖z‖ ≤ |M| := (mem_closedBall_zero_iff.1 (hM hz)).trans (le_abs_self M)
  rw [dist_zero_left, norm_neg, norm_inv] at hwd
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rw [inv_lt_comm₀ hpos (by positivity), one_div, inv_inv] at hwd
  linarith only [hzM, hwd]

/-- The relative chart has limit zero at its starting point. -/
theorem tendsto_relMap_zero {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (relMap U s) (𝓝[relDomain U s] (0 : ℂ)) (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := WangWu.exists_norm_fwdMap_sub_le hU hU0 hs
  have hI : Tendsto (fun w : ℂ => -w⁻¹) (𝓝[relDomain U s] (0 : ℂ)) (cobounded ℂ) :=
    Filter.tendsto_neg_cobounded.comp (tendsto_inv₀_nhdsNE_zero.mono_left
      (nhdsWithin_mono _ fun w hw => ne_zero_of_mem_H hw.1))
  have hF : Tendsto (fun w : ℂ => QuantumZipper.fwdMap U s (-w⁻¹))
      (𝓝[relDomain U s] (0 : ℂ)) (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-C)
      (tendsto_norm_atTop_iff_cobounded.2 hI))
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hD := Q3Rel.negInv_mem_compl hw
    have h1 := hC _ hD
    have h2 := norm_sub_norm_le (-w⁻¹) (QuantumZipper.fwdMap U s (-w⁻¹))
    rw [norm_sub_rev] at h2
    linarith only [h1, h2]
  have h := (tendsto_inv₀_cobounded.comp hF).neg
  rw [neg_zero] at h
  exact h.congr fun _ => rfl

theorem relBdry_zero {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) : relBdry U s 0 = 0 :=
  extendFrom_eq (relSafe_subset_closure_relDomain U s
    ⟨show (0 : ℂ) ∈ Hbar by change (0 : ℝ) ≤ 0; rfl, zero_notMem_closure_invHull hU hs⟩)
    (tendsto_relMap_zero hU hU0 hs)

/-- A real input off the retained hull has a real extended chart value. -/
theorem im_relBdry_of_real {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {x : ℝ} (hx : (x : ℂ) ∉ closure (invHull U s)) :
    (relBdry U s x).im = 0 := by
  obtain ⟨v, hv⟩ := Q3Rel.tendsto_relMap hU hU0 hs hx
  have he : relBdry U s x = (v : ℂ) := extendFrom_eq
    (relSafe_subset_closure_relDomain U s ⟨show (x : ℂ) ∈ Hbar by change (0 : ℝ) ≤ 0; rfl, hx⟩) hv
  rw [he, ofReal_im]

/-- The extension has an interior value precisely at interior safe inputs. -/
theorem relBdry_mem_H_iff {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ relSafe U s) :
    relBdry U s z ∈ H ↔ z ∈ H := by
  by_cases hzH : z ∈ H
  · rw [relBdry_eq hU hs hzH hz.2]
    exact iff_of_true (relMap_mem_H hU hs hzH (fun h => hz.2
      (subset_closure ⟨-z⁻¹, h, neg_inv_neg_inv z⟩))) hzH
  · have him : z.im = 0 := le_antisymm (not_lt.1 hzH) hz.1
    have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa only [ofReal_im] using him)
    have hb := im_relBdry_of_real hU hU0 hs (he ▸ hz.2)
    rw [← he] at hb
    exact iff_of_false (by change ¬0 < (relBdry U s z).im; rw [hb]; exact lt_irrefl _) hzH

/-- Real chart values add no interior points to a mapped prefix. -/
theorem image_relBdry_inter_H {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {A : Set ℂ} (hA : A ⊆ relSafe U s) :
    (relBdry U s '' A) ∩ H = relMap U s '' (A ∩ H) := by
  ext z
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hzH⟩
    have hwH := (relBdry_mem_H_iff hU hU0 hs (hA hw)).1 hzH
    exact ⟨w, ⟨hw, hwH⟩, (relBdry_eq hU hs hwH (hA hw).2).symm⟩
  · rintro ⟨w, ⟨hw, hwH⟩, rfl⟩
    have he := relBdry_eq hU hs hwH (hA hw).2
    refine ⟨⟨w, hw, he⟩, ?_⟩
    rw [← he]
    exact (relBdry_mem_H_iff hU hU0 hs (hA hw)).2 hwH

/-- The filling predicate depends only on the part of the generating set in `H`. -/
theorem isFilling_congr_inter_H {K A B : Set ℂ} (h : A ∩ H = B ∩ H) :
    IsFilling K A ↔ IsFilling K B := by
  have he : H \ A = H \ B := by
    ext z
    constructor
    · rintro ⟨hz, hn⟩
      exact ⟨hz, fun hb => hn ((Set.ext_iff.1 h z).2 ⟨hb, hz⟩).1⟩
    · rintro ⟨hz, hn⟩
      exact ⟨hz, fun ha => hn ((Set.ext_iff.1 h z).1 ⟨ha, hz⟩).1⟩
  unfold IsFilling
  rw [he]

/-- Adding the real boundary chart values preserves GB6's established filling. -/
theorem isFilling_relBdry_image {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {A K : Set ℂ} (hA : A ⊆ relSafe U s)
    (hfill : IsFilling K (relMap U s '' (A ∩ H))) : IsFilling K (relBdry U s '' A) := by
  have hsub : relMap U s '' (A ∩ H) ⊆ H := by
    rintro _ ⟨z, ⟨hz, hzH⟩, rfl⟩
    exact relMap_mem_H hU hs hzH fun h => (hA hz).2 (subset_closure ⟨-z⁻¹, h, neg_inv_neg_inv z⟩)
  have he : (relBdry U s '' A) ∩ H = (relMap U s '' (A ∩ H)) ∩ H := by
    rw [inter_eq_left.2 hsub]
    exact image_relBdry_inter_H hU hU0 hs hA
  exact (isFilling_congr_inter_H he).2 hfill

/-- The open compact-prefix reparametrization is driven. No condition that the
physical trace be in `H` at positive times is used. -/
theorem isDrivenCurve_relBdry {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {γ : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn γ (Ico 0 T)) (h0 : γ 0 = 0)
    (hsafe : MapsTo γ (Ico 0 T) (relSafe U s))
    (hloc : ∀ S : ℝ, 0 < S → S < T → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
      ∃ a : ℝ → ℝ, a 0 = 0 ∧ StrictMonoOn a (Icc 0 S) ∧ ContinuousOn a (Icc 0 S) ∧
        ∀ t ∈ Icc 0 S, 0 ≤ a t ∧
          IsFilling (fwdHull W (a t)) (relMap U s '' (γ '' Icc 0 t ∩ H))) :
    Sec7.PocketTraversal.IsDrivenCurve
      (Sec7.PocketTraversal.relCurve (fun t => relBdry U s (γ t)) T) := by
  apply Sec7.PocketTraversal.isDrivenCurve_relCurve hT
    (continuousOn_relBdry_comp hU hU0 hs hc hsafe) (by rw [h0, relBdry_zero hU hU0 hs])
  intro S hS hST
  obtain ⟨W, hW, hW0, a, ha0, ham, hac, hK⟩ := hloc S hS hST
  refine ⟨W, hW, hW0, a, ha0, ham, hac, fun t ht => ?_⟩
  have hsub : γ '' Icc 0 t ⊆ relSafe U s := by
    rintro _ ⟨u, hu, rfl⟩
    exact hsafe ⟨hu.1, (hu.2.trans ht.2).trans_lt hST⟩
  have hfill := isFilling_relBdry_image hU hU0 hs hsub (hK t ht).2
  have hcomp : IsCompact ((fun t => relBdry U s (γ t)) '' Icc 0 t) :=
    isCompact_Icc.image_of_continuousOn
      ((continuousOn_relBdry_comp hU hU0 hs hc hsafe).mono fun u hu =>
        ⟨hu.1, (hu.2.trans ht.2).trans_lt hST⟩)
  rw [image_image] at hfill
  exact (fillH_eq_iff_isFilling_of_isClosed hcomp.isBounded hcomp.isClosed
    (fun z hz => hz.1)).1 hfill

end InteractingSLE.Supp8.GB6.CoordB
