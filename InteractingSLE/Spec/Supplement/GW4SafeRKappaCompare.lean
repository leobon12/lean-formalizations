/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaCommon

/-! # GW4: compare the integers of two current charts through one collar -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap logDerivFwd)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.R5Lift

/-- A reflected old collar surviving to the later ambient time has zero
ambient logarithm increment. The ambient boundary value may be zero; no
side or fresh-tip assumption is needed for this phase comparison. -/
theorem tendsto_ambient_lift_increment_zero_of_collar {cur old : Chart}
    (hcur : cur.IsConformal) (hold : old.IsConformal)
    {Fo : ℂ → ℂ} (hFo : EqOn Fo old.2.1 H) (hFoc : ContinuousOn Fo Hbar)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T)
    (hKT : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T)
    (hKs : (old.dom : Set ℂ) ⊆ H \ fwdHull W s)
    {ξ x ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (hcol : old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ cur.dom)
    (hland : ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → Fo u ∉ H \ fwdHull W s)
    {x' : ℝ}
    (hfx : Tendsto (fun y => fwdMap W s (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)))
    (hfo : Tendsto (fun y => fwdMap W s (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ))) :
    Tendsto (fun y => (logDerivFwd W T (cur.2.1 y)).im -
      (logDerivFwd W s (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  let r := min ρ ε
  have hr : 0 < r := lt_min hρ hε
  obtain ⟨hgΦ, hgc, hgreal, hmaps, hinj, hgd, hglim⟩ := reflect_data_of_notMem
    (x := x) (ρ := r) hold hFo hFoc hη hW hW0 hs hKs
    (fun u hu => hland u (ball_subset_ball (min_le_left _ _) hu))
  have := nhdsWithin_H_neBot x
  have hgx := tendsto_nhds_unique (hglim x
    ⟨show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im], mem_ball_self hr⟩) hfo
  obtain ⟨ρ', hρ', hsub⟩ := exists_halfBall_subset_image_of_reflect hr hgd hgc hgreal hmaps hinj
  rw [hgx] at hsub
  have hsub' : H ∩ ball (x' : ℂ) ρ' ⊆ fwdMap W s '' (H \ fwdHull W T) := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hsub hz
    refine ⟨old.2.1 v, hKT (hcol ⟨v, ⟨hv.1, ball_subset_ball (min_le_right _ _) hv.2⟩, rfl⟩), hgΦ hv⟩
  exact tendsto_im_logDerivFwd_sub_of_notMem_closure hW hs hsT
    (eventually_nhdsWithin_of_forall fun y hy => hKT (hcur.inv_mem_dom hy)) hfx
    (notMem_closure_incrHull_of_subset_image hW hs hsT hρ' hsub')

/-- Two current winding integers agree whenever their accesses are joined
by a surviving old collar with zero inherited own lift. -/
theorem phase_int_eq_of_collar {cur old : Chart} (hcur : cur.IsConformal) (hold : old.IsConformal)
    {Fo : ℂ → ℂ} (hFo : EqOn Fo old.2.1 H) (hFoc : ContinuousOn Fo Hbar)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T)
    (hKT : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T)
    (hKs : (old.dom : Set ℂ) ⊆ H \ fwdHull W s)
    (hincl : (cur.dom : Set ℂ) ⊆ old.dom)
    {ξ x ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (hcol : old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ cur.dom)
    (hland : ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → Fo u ∉ H \ fwdHull W s)
    (htr : Tendsto (fun y => old.1 (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)))
    (hlift : Tendsto (fun y => cur.2.2 (cur.2.1 y) - old.2.2 (cur.2.1 y))
      (𝓝[H] (ξ : ℂ)) (𝓝 0)) {m n : ℤ}
    (hm : Tendsto (fun y => old.2.2 (old.2.1 y) - (logDerivFwd W s (old.2.1 y)).im)
      (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * m)))
    (hn : Tendsto (fun y => cur.2.2 (cur.2.1 y) - (logDerivFwd W T (cur.2.1 y)).im)
      (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n))) : m = n := by
  have htrH : Tendsto (fun y => old.1 (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨htr, eventually_nhdsWithin_of_forall fun y hy =>
      hold.fwd_mem (hincl (hcur.inv_mem_dom hy))⟩
  have hcancel : ∀ y ∈ H, old.2.1 (old.1 (cur.2.1 y)) = cur.2.1 y := fun y hy =>
    hold.inv_fwd (hincl (hcur.inv_mem_dom hy))
  have hOld : Tendsto (fun y => old.2.2 (cur.2.1 y) - (logDerivFwd W s (cur.2.1 y)).im)
      (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * m)) :=
    (hm.comp htrH).congr' (eventually_nhdsWithin_of_forall fun y hy => by
      simp only [Function.comp_apply, hcancel y hy])
  have hOld' : Tendsto (fun y => cur.2.2 (cur.2.1 y) - (logDerivFwd W s (cur.2.1 y)).im)
      (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * m)) := by
    have h := hlift.add hOld
    rw [zero_add] at h
    exact h.congr fun _ => by ring
  obtain ⟨-, -, hreal, -, -, -, hlim⟩ := reflect_data_of_notMem (x := x) (ρ := ρ)
    hold hFo hFoc hη hW hW0 hs hKs hland
  let x' : ℝ := (extendFrom H (fun y => fwdMap W s (old.2.1 y)) x).re
  have hx' : (extendFrom H (fun y => fwdMap W s (old.2.1 y)) x) = (x' : ℂ) :=
    Complex.ext rfl (by rw [ofReal_im]; exact hreal _ (mem_ball_self hρ) (ofReal_im x))
  have hfo : Tendsto (fun y => fwdMap W s (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
    rw [← hx']
    exact hlim x ⟨show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im], mem_ball_self hρ⟩
  have hfx : Tendsto (fun y => fwdMap W s (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) :=
    (hfo.comp htrH).congr' (eventually_nhdsWithin_of_forall fun y hy => by
      simp only [Function.comp_apply, hcancel y hy])
  have hz := tendsto_ambient_lift_increment_zero_of_collar hcur hold hFo hFoc hη hW hW0 hs hsT
    hKT hKs hε hρ hcol hland hfx hfo
  have hNew : Tendsto (fun y => cur.2.2 (cur.2.1 y) - (logDerivFwd W s (cur.2.1 y)).im)
      (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) := by
    have h := hn.add hz
    rw [add_zero] at h
    exact h.congr fun _ => by ring
  have := nhdsWithin_H_neBot ξ
  have heq := tendsto_nhds_unique hOld' hNew
  have hmn : (m : ℝ) = n := mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) heq
  exact_mod_cast hmn

end InteractingSLE.Theorem14.GW4Fix
