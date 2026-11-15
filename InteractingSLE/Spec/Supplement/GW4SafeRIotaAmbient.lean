/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfSide

/-! # GW4: ambient access at hull and real boundary landings

The landed bounded-composition argument only needs the landing outside
the ambient open domain. This includes landings on the original real
line as well as landings in the hull.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7 ZhanGT4

/-- A finite physical landing gives a finite transition limit in the closed
half-plane. This form also includes physical landings in the ambient open
domain; no boundary-side assertion is imposed. -/
theorem exists_ambient_transition_limit {w : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace w η) (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) {old : Chart} (hOld : old.IsConformal) (hOldDom : (old.dom : Set ℂ) ⊆ H \ fwdHull w s)
    {x : ℝ} {p : ℂ} (hLanding : Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) :
    ∃ y : ℂ, y ∈ Hbar ∧ extendFrom H (fwdMapInv w s) y = p ∧
      Tendsto (fun z => fwdMap w s (old.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 y) := by
  set F := extendFrom H (fwdMapInv w s) with hFdef
  have hFeq : EqOn F (fwdMapInv w s) H := fun z hz => extendFrom_eq_fwdMapInv hw hw0 hs hz
  have hB := isBoundaryMap_extendFrom hη hw hw0 hs
  have hd : DifferentiableOn ℂ F H :=
    (isConformalBijection_fwdMapInv hw hw0 hs).1.congr fun z hz => hFeq hz
  have hR : ∀ z : ℂ, z.im = 0 → F z ∉ F '' H := by
    intro z hz
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
    rw [hz']
    exact extendFrom_not_mem_image hη hw hw0 hs le_rfl z.re
  have hmaps : ∀ z ∈ H, old.2.1 z ∈ H \ fwdHull w s := fun z hz => hOldDom (hOld.inv_mem_dom hz)
  have hGc : ContinuousOn (fun z => fwdMap w s (old.2.1 z)) (H ∩ ball (x : ℂ) 1) :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs).continuousOn.comp hOld.1.continuousOn
      fun z hz => hmaps z hz).mono inter_subset_left
  have hGH : MapsTo (fun z => fwdMap w s (old.2.1 z)) (H ∩ ball (x : ℂ) 1) Hbar := fun z hz =>
    QuantumZipper.H_subset_Hbar (QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (hmaps z hz.1))
  have hbd : ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (x : ℂ), ‖old.2.1 z‖ ≤ M := by
    refine ⟨‖p‖ + 1, ?_⟩
    filter_upwards [hLanding.eventually (ball_mem_nhds p one_pos)] with z hz
    have hn := norm_sub_norm_le (old.2.1 z) p
    rw [dist_eq_norm] at hz
    linarith
  obtain ⟨M, hM⟩ := PocketStopSide.eventually_norm_bounded_loewner_comp hw hw0 hs
    (eventually_nhdsWithin_of_forall fun z hz => hmaps z hz) hbd
  have hFG : Tendsto (fun z => F (fwdMap w s (old.2.1 z))) (𝓝[H] (x : ℂ)) (𝓝 p) :=
    hLanding.congr' (eventually_nhdsWithin_of_forall fun z hz => by
      show old.2.1 z = F (fwdMap w s (old.2.1 z))
      rw [hFeq (QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (hmaps z hz)),
        QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 hs (hmaps z hz)])
  obtain ⟨y, hy, hFy, hlim⟩ :=
    PocketStopSide.exists_tendsto_of_tendsto_comp_local hd hB.cont hB.inj hR one_pos hGc hGH hM hFG
  exact ⟨y, hy, hFy, hlim⟩

/-- The actual conformal transition has a finite real boundary value at
any finite landing outside the ambient open domain. -/
theorem exists_ambient_access_of_notMem {w : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace w η) (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) {old : Chart} (hOld : old.IsConformal) (hOldDom : (old.dom : Set ℂ) ⊆ H \ fwdHull w s)
    {x : ℝ} {p : ℂ} (hLanding : Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) (hpK : p ∉ H \ fwdHull w s) :
    ∃ x' : ℝ, extendFrom H (fwdMapInv w s) (x' : ℂ) = p ∧
      Tendsto (fun z => fwdMap w s (old.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  obtain ⟨y, hy, hFy, hlim⟩ := exists_ambient_transition_limit hη hw hw0 hs hOld hOldDom hLanding
  have hFeq : EqOn (extendFrom H (fwdMapInv w s)) (fwdMapInv w s) H := fun z hz =>
    extendFrom_eq_fwdMapInv hw hw0 hs hz
  have hy0 : y.im = 0 := by
    rcases (show 0 ≤ y.im from hy).lt_or_eq with hpos | h
    · exfalso
      have hyH : y ∈ H := hpos
      have hc := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 hs hyH
      rw [← hFeq hyH, hFy] at hc
      exact hpK hc
    · exact h.symm
  have hyr : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [hy0])
  refine ⟨y.re, ?_, ?_⟩
  · rw [← hyr]
    exact hFy
  · rwa [← hyr]

end InteractingSLE.Theorem14.GW4Fix
