/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInReachLimit
import InteractingSLE.Spec.Supplement.WalkIntGermChart
import InteractingSLE.Spec.Supplement.WalkPieceProof

/-!
# Physical landings determine finite prefix transition limits

The local Yuan fibre theorem is reused for a finite chart with a proper
inverse extension. Its bounded displacement supplies the transition bound.
Only a half-disc, rather than the whole component, must lie in that chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntFiber

/-- A physical landing and a local common domain give a finite transition
limit. A boundary landing of the reference chart gives a real limit. -/
theorem exists_transition_limit_of_landing {c d : Chart}
    (hc : c.IsConformal) (hd : d.IsConformal) (hproper : GW1P.HasProperBdryExt d)
    {x r : ℝ} (hr : 0 < r)
    (hdom : ∀ z ∈ H ∩ ball (x : ℂ) r, c.2.1 z ∈ d.dom)
    {p : ℂ} (hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) :
    ∃ v ∈ Hbar, Tendsto (fun z => d.1 (c.2.1 z))
      (𝓝[H] (x : ℂ)) (𝓝 v) ∧ (p ∉ d.dom → v.im = 0) := by
  obtain ⟨E, M, hE, hM⟩ := hproper
  have heq : EqOn E d.2.1 H := fun _ hz => WalkPiece.bdry_eq_inv_of_mem_H hd hE hz
  have hEc := GW1P.continuousOn_of_tendsto hE
  have hevent : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H ∩ ball (x : ℂ) r :=
    inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hr)
  have hbound : ∀ᶠ z in 𝓝[H] (x : ℂ), ‖d.1 (c.2.1 z)‖ ≤ ‖p‖ + 1 + M := by
    filter_upwards [hevent, hland (ball_mem_nhds p one_pos)] with z hz hzp
    have hT := hd.fwd_mem (hdom z hz)
    have hb := hM _ (QuantumZipper.H_subset_Hbar hT)
    rw [heq hT, hd.inv_fwd (hdom z hz)] at hb
    have hp : ‖c.2.1 z‖ ≤ ‖p‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (c.2.1 z) p
      change c.2.1 z ∈ ball p 1 at hzp
      rw [mem_ball, dist_eq_norm] at hzp
      linarith
    have := norm_le_norm_add_norm_sub' (d.1 (c.2.1 z)) (c.2.1 z)
    rw [norm_sub_rev (d.1 (c.2.1 z)) (c.2.1 z)] at this
    linarith
  have hcomp : Tendsto (fun z => E (d.1 (c.2.1 z)))
      (𝓝[H] (x : ℂ)) (𝓝 p) := by
    refine hland.congr' ?_
    filter_upwards [hevent] with z hz
    exact ((heq (hd.fwd_mem (hdom z hz))).trans (hd.inv_fwd (hdom z hz))).symm
  obtain ⟨v, hv, hEv, hlim⟩ := Sec7.PocketStopSide.exists_tendsto_of_tendsto_comp_local
    (hd.1.congr (fun _ hz => heq hz)) hEc (hd.injOn.congr heq.symm)
    (Sec7.PocketStopSide.inverse_extension_real_notMem_image hd heq hEc) hr
    (hd.differentiableOn_fwd.continuousOn.comp
      (hc.1.continuousOn.mono inter_subset_left) hdom)
    (fun _ hz => QuantumZipper.H_subset_Hbar (hd.fwd_mem (hdom _ hz))) hbound hcomp
  refine ⟨v, hv, hlim, fun hp => le_antisymm (not_lt.1 fun hvH => hp ?_) hv⟩
  rw [← hEv, heq hvH]
  exact hd.inv_mem_dom hvH

theorem exists_real_transition_limit_of_landing {c d : Chart}
    (hc : c.IsConformal) (hd : d.IsConformal) (hproper : GW1P.HasProperBdryExt d)
    {x r : ℝ} (hr : 0 < r)
    (hdom : ∀ z ∈ H ∩ ball (x : ℂ) r, c.2.1 z ∈ d.dom)
    {p : ℂ} (hp : p ∉ d.dom)
    (hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) :
    ∃ v : ℂ, v.im = 0 ∧ Tendsto (fun z => d.1 (c.2.1 z))
      (𝓝[H] (x : ℂ)) (𝓝 v) := by
  obtain ⟨v, -, hlim, hv⟩ := exists_transition_limit_of_landing hc hd hproper hr hdom hland
  exact ⟨v, hv hp, hlim⟩

end InteractingSLE.Theorem14.WalkIntFiber
