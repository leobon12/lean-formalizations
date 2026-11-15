/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71OWall
import InteractingSLE.Spec.Restart.ClockCap

/-!
# Lemma 7.1's inherited branch: the union of two wall prefixes

Packet PROVE-LEMMA71O (supplement §2.3, proof of the deterministic normalization lemma, `source/spec/p433-480.md`
L496–L512: "Retain the left prefix … and the right prefix … Fill their union and let `D_p` be its unbounded
complementary domain, with hydrodynamic map `g_p`. The pocket `C` lies in `D_p`").

* `exists_tendsto_mapOut_comp`: if a compact set `Γ` agrees near the landing point with a wall prefix `η([0, q])`,
  and the wall transition `f_q ∘ c.2.1` has a real limit, then the transition `g_Γ ∘ c.2.1` of the map of `fill Γ`
  has a real limit too (`g_Γ = g_{C'} ∘ g_A` with `g_{C'}` reflecting across the image of the approach: the half-disc
  lemma `ReverseArc.exists_ball_notMem_of_approach`);
* `subset_H_diff_fillH_of_escape`: a connected set off `Γ` joined through one point to a connected unbounded set off
  `Γ` lies in the unbounded domain of `Γ`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71O

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

section Union

variable {c : Chart}

/-- **The transition of the union map has a real limit where the union agrees with one wall prefix.** -/
theorem exists_tendsto_mapOut_comp {Γ : Set ℂ} (hΓc : IsCompact Γ) (hKΓ : IsHPHull (fillH Γ)) {gK : ℂ → ℂ}
    (hgK : IsMapOut (fillH Γ) gK) (hc : c.IsConformal) (hCΓ : (c.dom : Set ℂ) ⊆ H \ fillH Γ) {x p : ℂ}
    (hx : x ∈ Hbar) (hland : Tendsto c.2.1 (𝓝[H] x) (𝓝 p)) {ρ : ℝ} (hρ : 0 < ρ) {η : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}
    (htr : IsGeneratingTrace W ⊤ η) (hW : Continuous W) (hW0 : W 0 = 0) (hηi : Function.Injective η) {q : ℝ≥0}
    (hq0 : 0 < q) (hsub : η '' Icc 0 q ⊆ Γ) (hloc : Γ ∩ ball p ρ ⊆ η '' Icc 0 q) {v : ℂ} (hv : v.im = 0)
    (hT : Tendsto (fun y => fwdMap (fun r : ℝ => W r.toNNReal) q (c.2.1 y)) (𝓝[H] x) (𝓝 v)) :
    ∃ w : ℂ, w.im = 0 ∧ Tendsto (fun y => gK (c.2.1 y)) (𝓝[H] x) (𝓝 w) := by
  have hg : IsGeneratingTrace W ⊤ (fun t => η t - ((0 : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htr
  obtain ⟨κ, hA, hgA, -⟩ := ReverseArc.exists_physChart hg hW.continuousOn hW0 (WithTop.coe_lt_top q)
  obtain ⟨Φ, hΦc, hΦH, -, hinv, hmaps⟩ :=
    ReverseArc.exists_physInv hg hW.continuousOn hW0 hηi.injOn (WithTop.coe_lt_top q) hq0
  simp only [Complex.ofReal_zero, sub_zero] at hgA hinv hmaps
  set f : ℂ → ℂ := fun z => fwdMap (fun r : ℝ => W r.toNNReal) q z with hfdef
  set A := fillH (η '' Icc 0 q) with hAdef
  have hAΓ : A ⊆ fillH Γ := fillH_mono hsub
  have hvr : v = ((v.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero hv
  -- the half-disc lemma along one ultrafilter
  have hNe : (𝓝[H] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hx)
  set U : Ultrafilter ℂ := Ultrafilter.of (𝓝[H] x) with hUdef
  have hU : (U : Filter ℂ) ≤ 𝓝[H] x := Ultrafilter.of_le _
  set V : Ultrafilter ℂ := U.map c.2.1 with hVdef
  have hVle : (V : Filter ℂ) ≤ 𝓝[H \ fillH Γ] p := by
    rw [hVdef, Ultrafilter.coe_map]
    refine tendsto_nhdsWithin_iff.2 ⟨hland.mono_left hU, ?_⟩
    have hH : ∀ᶠ y in (U : Filter ℂ), y ∈ H := hU self_mem_nhdsWithin
    exact hH.mono fun y hy => hCΓ (hc.inv_mem_dom hy)
  have hfV : Tendsto f (V : Filter ℂ) (𝓝 ((v.re : ℝ) : ℂ)) := by
    rw [hVdef, Ultrafilter.coe_map, ← hvr]
    exact tendsto_map'_iff.2 (hT.mono_left hU)
  obtain ⟨ε, hε, hno⟩ := ReverseArc.exists_ball_notMem_of_approach hΓc.isClosed hsub hmaps hΦc hΦH hinv hρ
    hloc V hVle hfV
  -- the factorization `g_Γ = g_{C'} ∘ g_A`
  set gA : ℂ → ℂ := fun z => f z + κ with hgAdef
  set C' := gA '' (fillH Γ \ A) with hC'def
  have hC' : IsHPHull C' := hgA.isHPHull_image hA hKΓ hAΓ
  set gC := ConformalImage.mapOut C' with hgCdef
  have hgC : IsMapOut C' gC := ConformalImage.isMapOut_mapOut hC'
  have hcomp : IsMapOut (fillH Γ) (gC ∘ gA) := hgA.comp hA hKΓ hAΓ hgC
  have heq : EqOn gK (gC ∘ gA) (H \ fillH Γ) := hgK.eqOn hKΓ hcomp
  set y₀ : ℝ := v.re + κ with hy₀
  have hd : Disjoint (ball (y₀ : ℂ) ε) C' := by
    rw [Set.disjoint_left]
    rintro w hwb ⟨z, ⟨hzΓ, hzA⟩, rfl⟩
    refine hno z ⟨hKΓ.1 hzΓ, hzA⟩ hzΓ ?_
    rw [mem_ball, dist_eq_norm] at hwb ⊢
    convert hwb using 2
    simp only [hgAdef, hy₀]; push_cast; ring
  obtain ⟨w, hw0, hwlim⟩ := hgC.exists_tendsto_of_disjoint hC' hd (mem_ball_self (by positivity))
    (by simp)
  refine ⟨w, hw0, ?_⟩
  -- the inner transition tends to `y₀` inside the half-disc
  have hinner : Tendsto (fun y => gA (c.2.1 y)) (𝓝[H] x) (𝓝[ball (y₀ : ℂ) (ε / 2) ∩ H] (y₀ : ℂ)) := by
    have h1 : Tendsto (fun y => gA (c.2.1 y)) (𝓝[H] x) (𝓝 (y₀ : ℂ)) := by
      have := hT.add_const (κ : ℂ)
      rw [hvr] at this
      convert this using 2
      rw [hy₀]; push_cast; ring
    refine tendsto_nhdsWithin_iff.2 ⟨h1, ?_⟩
    filter_upwards [h1 (ball_mem_nhds _ (by positivity : (0 : ℝ) < ε / 2)), self_mem_nhdsWithin] with y hyb hy
    refine ⟨hyb, ?_⟩
    have hz : c.2.1 y ∈ H \ A := ⟨(hCΓ (hc.inv_mem_dom hy)).1, fun h => (hCΓ (hc.inv_mem_dom hy)).2 (hAΓ h)⟩
    exact hgA.1.2.mapsTo hz
  refine (hwlim.comp hinner).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  exact (heq (hCΓ (hc.inv_mem_dom hy))).symm

/-- **Escape to infinity**: a preconnected set `C` off `Γ`, joined through a point `w₀ ∉ Γ` of `ℍ` adherent to both, to
a preconnected unbounded set `R ⊆ ℍ ∖ Γ`, lies in the unbounded domain of the bounded set `Γ`. -/
theorem subset_H_diff_fillH_of_escape {Γ C R : Set ℂ} (hΓc : IsClosed Γ) (hC : IsPreconnected C)
    (hCΓ : C ⊆ H \ Γ) (hR : IsPreconnected R) (hRΓ : R ⊆ H \ Γ) (hRb : ¬ Bornology.IsBounded R) {w₀ : ℂ}
    (hw₀ : w₀ ∈ H \ Γ) (hw₀C : w₀ ∈ closure C) (hw₀R : w₀ ∈ closure R) : C ⊆ H \ fillH Γ := by
  intro z hz
  have hS : IsPreconnected (insert w₀ C ∪ insert w₀ R) := by
    refine (hC.subset_closure (subset_insert _ _) (insert_subset hw₀C subset_closure)).union w₀
      (mem_insert _ _) (mem_insert _ _) (hR.subset_closure (subset_insert _ _) (insert_subset hw₀R subset_closure))
  have hSΓ : insert w₀ C ∪ insert w₀ R ⊆ H \ closure Γ := by
    rw [hΓc.closure_eq]
    rintro u ((rfl | hu) | (rfl | hu))
    · exact hw₀
    · exact hCΓ hu
    · exact hw₀
    · exact hRΓ hu
  have hcomp : insert w₀ C ∪ insert w₀ R ⊆ connectedComponentIn (H \ closure Γ) z :=
    hS.subset_connectedComponentIn (Or.inl (mem_insert_of_mem _ hz)) hSΓ
  refine ⟨(hCΓ hz).1, fun hzf => ?_⟩
  rcases hzf.2 with hzc | hbd
  · rw [hΓc.closure_eq] at hzc; exact (hCΓ hz).2 hzc
  · exact hRb (hbd.subset ((subset_insert w₀ R).trans (subset_union_right.trans hcomp)))

end Union

end InteractingSLE.Sec7.Lemma71O
