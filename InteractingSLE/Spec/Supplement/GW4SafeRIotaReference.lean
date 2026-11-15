/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaReflect

/-! # GW4: compare each reference with the current chart, including real landings -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap logDerivFwd)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.R5Lift

/-- Compare one reference with the current ambient time at its own surviving
collar. Boundary landings may lie on the original real line. The proof uses
reflection at that collar and the zero lift of an unfilled ambient increment;
references need not be directed. -/
theorem ref_lift_side_of_cur_notMem {cur old : Chart} (hcur : cur.IsConformal) (hold : old.IsConformal)
    {Fc Fo : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H) (hFcc : ContinuousOn Fc Hbar) (hFo : EqOn Fo old.2.1 H)
    (hFoc : ContinuousOn Fo Hbar)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {s T : ℝ}
    (hs : 0 ≤ s) (hT : 0 ≤ T)
    (hKT : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T) (hKs : (old.dom : Set ℂ) ⊆ H \ fwdHull W s)
    (hincl : (cur.dom : Set ℂ) ⊆ old.dom) {ξ x ε x' : ℝ} (hε : 0 < ε)
    (hcol : old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ cur.dom)
    (hlandT : ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (ξ : ℂ) ρ → Fc v ∉ H \ fwdHull W T)
    (hlandS : ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → Fo u ∉ H \ fwdHull W s) (hx'0 : x' ≠ 0)
    (hfx : Tendsto (fun y => fwdMap W s (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)))
    (hfo : Tendsto (fun y => fwdMap W s (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ))) {A : ℂ → ℝ} {d : ℝ}
    (hn : Tendsto (fun y => A (cur.2.1 y) - (logDerivFwd W T (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 d))
    (hside : ∀ y : ℝ, Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (y : ℂ)) →
      (ξ < 0 ↔ y < 0)) :
    Tendsto (fun y => A (cur.2.1 y) - (logDerivFwd W s (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
      (ξ < 0 ↔ x' < 0) := by
  have := nhdsWithin_H_neBot ξ
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), cur.2.1 y ∈ H \ fwdHull W T :=
    eventually_nhdsWithin_of_forall fun y hy => hKT (hcur.inv_mem_dom hy)
  have hcurKs : ∀ᶠ y in 𝓝[H] (ξ : ℂ), cur.2.1 y ∈ H \ fwdHull W s :=
    eventually_nhdsWithin_of_forall fun y hy => hKs (hincl (hcur.inv_mem_dom hy))
  rcases le_total s T with hsT | hTs
  · -- the old transition covers a half-disc about `x′`, inside `f_s(ℍ ∖ K_T)`
    obtain ⟨ρ, hρ, hlandK⟩ := hlandS
    set r := min ρ ε with hr
    have hr0 : 0 < r := lt_min hρ hε
    obtain ⟨hgΦ, hgc, hgreal, hmaps, hinj, hgd, hglim⟩ := reflect_data_of_notMem (x := x) (ρ := r) hold
      hFo hFoc hη hW hW0 hs hKs fun u hu => hlandK u (ball_subset_ball (min_le_left _ _) hu)
    have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im]
    have := nhdsWithin_H_neBot x
    have hgx := tendsto_nhds_unique (hglim x ⟨hxbar, mem_ball_self hr0⟩) hfo
    obtain ⟨ρ', hρ', hsub⟩ := exists_halfBall_subset_image_of_reflect hr0 hgd hgc hgreal hmaps hinj
    rw [hgx] at hsub
    have hsub' : H ∩ ball (x' : ℂ) ρ' ⊆ fwdMap W s '' (H \ fwdHull W T) := by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := hsub hw
      refine ⟨old.2.1 z, hKT (hcol ⟨z, ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩, rfl⟩), ?_⟩
      exact hgΦ hz
    have hxK := notMem_closure_incrHull_of_subset_image hW hs hsT hρ' hsub'
    have hcomp := tendsto_im_logDerivFwd_sub_of_notMem_closure hW hs hsT hcurK hfx hxK
    refine ⟨?_, ?_⟩
    · have h := hn.add hcomp
      rw [add_zero] at h
      exact h.congr fun y => by ring
    · obtain ⟨y, hy, hyside⟩ := tendsto_fwdMap_of_alive hW hs hsT hcurK hx'0 hfx hxK
      exact (hside y hy).trans hyside
  · -- the current transition at time `T` covers a half-disc inside `f_T(ℍ ∖ K_s)`
    obtain ⟨ρ, hρ, hlandK⟩ := hlandT
    obtain ⟨hgΦ, hgc, hgreal, hmaps, hinj, hgd, hglim⟩ := reflect_data_of_notMem (x := ξ) (ρ := ρ) hcur
      hFc hFcc hη hW hW0 hT hKT hlandK
    have hξbar : (ξ : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (ξ : ℂ).im by rw [ofReal_im]
    set g := extendFrom H fun y => fwdMap W T (cur.2.1 y) with hg
    set y₀ : ℝ := (g ξ).re with hy₀
    have hgreal' : g ξ = (y₀ : ℂ) :=
      Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im]; exact hgreal _ (mem_ball_self hρ) (ofReal_im ξ))
    have hy₀T : Tendsto (fun y => fwdMap W T (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (y₀ : ℂ)) := by
      rw [← hgreal']; exact hglim ξ ⟨hξbar, mem_ball_self hρ⟩
    obtain ⟨ρ', hρ', hsub⟩ := exists_halfBall_subset_image_of_reflect hρ hgd hgc hgreal hmaps hinj
    rw [hgreal'] at hsub
    have hsub' : H ∩ ball (y₀ : ℂ) ρ' ⊆ fwdMap W T '' (H \ fwdHull W s) := by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := hsub hw
      exact ⟨cur.2.1 z, hKs (hincl (hcur.inv_mem_dom hz.1)), (hgΦ hz)⟩
    have hyK := notMem_closure_incrHull_of_subset_image hW hT hTs hρ' hsub'
    have hcomp := tendsto_im_logDerivFwd_sub_of_notMem_closure hW hT hTs hcurKs hy₀T hyK
    refine ⟨?_, ?_⟩
    · have h := hn.sub hcomp
      rw [sub_zero] at h
      exact h.congr fun y => by ring
    · have hy₀0 : y₀ ≠ 0 := by
        rcases hTs.lt_or_eq with hlt | heq
        · intro h0
          apply hyK
          rw [h0, ofReal_zero]
          exact ConformalImageFull.zero_mem_closure_fwdHull
            ((hW.comp (continuous_const.add continuous_id)).sub continuous_const) (by simp) (sub_pos.2 hlt)
        · subst heq
          have h1 : (y₀ : ℂ) = (x' : ℂ) := tendsto_nhds_unique hy₀T hfx
          have h2 : y₀ = x' := by exact_mod_cast h1
          exact fun h0 => hx'0 (h2 ▸ h0)
      obtain ⟨z, hz, hzside⟩ := tendsto_fwdMap_of_alive hW hT hTs hcurKs hy₀0 hy₀T hyK
      have hzx : z = x' := by exact_mod_cast tendsto_nhds_unique hz hfx
      rw [hzx] at hzside
      exact (hside y₀ hy₀T).trans hzside.symm

end InteractingSLE.Theorem14.GW4Fix
