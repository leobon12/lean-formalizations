/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC8Geometry
import InteractingSLE.Spec.Sec7.SideHeightLift

/-!
# GW4: actual inherited transition branches at surviving real accesses

The reflection, its radius and the boundary logarithm are constructed from
a surviving real characteristic. No collar or branch certificate is assumed.
The logarithm is the difference of the two canonical Loewner logarithms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Sec7 Sec7.PocketStopSide

/-- The actual transition hull at two own times has a positive reflection
at a surviving real access. The inherited complex logarithm tends to the
real logarithm of that derivative, with its exact zero argument. -/
theorem exists_transition_branch_of_surviving_real {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {s t x : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) {a : ℝ → ℂ}
    (ha : QuantumZipper.IsForwardSol W x t a) :
    let C := (fun z => fwdMap W s z + (W s : ℂ)) ''
      (fwdHull W t \ fwdHull W s)
    ∃ (g G : ℂ → ℂ) (r : ℝ), IsMapOut C g ∧
      IsBdryReflection C g G ((a s).re + W s) r ∧
      (deriv G ((a s).re + W s : ℝ)).im = 0 ∧
      0 < (deriv G ((a s).re + W s : ℝ)).re ∧
      Tendsto (fun y => logDerivFwd W t (fwdMapInv W t y) -
          logDerivFwd W s (fwdMapInv W t y))
        (𝓝[H] ((a t).re : ℂ))
        (𝓝 (Complex.log (deriv G ((a s).re + W s : ℝ)))) ∧
      Tendsto (fun y => (logDerivFwd W t (fwdMapInv W t y) -
          logDerivFwd W s (fwdMapInv W t y)).im)
        (𝓝[H] ((a t).re : ℂ)) (𝓝 0) := by
  dsimp only
  have ht := hs.trans hst
  obtain ⟨ε, hε, hCol, hTr, -⟩ :=
    exists_own_collar_of_surviving_real Chart.isConformal_id hW hW0 hs hst ha
  have hClear := disjoint_own_increment_of_inverse_halfDisc
    Chart.isConformal_id hW hW0 hs ht hCol
  let gA : ℂ → ℂ := fun z => fwdMap W s z + (W s : ℂ)
  let C := gA '' (fwdHull W t \ fwdHull W s)
  have hDisj : Disjoint (ball (((a s).re + W s : ℝ) : ℂ) ε) C := by
    refine disjoint_left.2 ?_
    rintro y hy ⟨z, hz, rfl⟩
    apply disjoint_left.1 hClear _ (mem_image_of_mem _ hz)
    simpa only [gA, mem_ball, ofReal_add, dist_add_right] using hy
  have hA := isHPHull_fwdHull hW hs
  have hB := isHPHull_fwdHull hW ht
  have hAB : fwdHull W s ⊆ fwdHull W t := QuantumZipper.fwdHull_mono.1 hst
  have hgA : IsMapOut (fwdHull W s) gA := isMapOut_fwdMap hW hW0 hs
  have hgB := isMapOut_fwdMap hW hW0 ht
  have hC : IsHPHull C := hgA.isHPHull_image hA hB hAB
  let g := ConformalImage.mapOut C
  have hg : IsMapOut C g := ConformalImage.isMapOut_mapOut hC
  obtain ⟨L, hL⟩ := exists_isCanonicalDerivLog hC hg
  obtain ⟨G, hG⟩ := exists_isBdryReflection hC hg hε hDisj
  obtain ⟨him, hpos⟩ := hG.deriv_im_eq_zero_and_re_pos hg
  have hLA := SideHeight.isCanonicalDerivLog_fwdMap hW hW0 hs
  have hLB := SideHeight.isCanonicalDerivLog_fwdMap hW hW0 ht
  have hComp := IsCanonicalDerivLog.comp hA hB hAB hgA hg hLA hL
  have hgComp : IsMapOut (fwdHull W t) (g ∘ gA) := hgA.comp hA hB hAB hg
  have hEq : EqOn (logDerivFwd W t)
      (fun z => L (gA z) + logDerivFwd W s z) (H \ fwdHull W t) :=
    IsCanonicalDerivLog.eqOn (hLB.congr hB (hgB.eqOn hB hgComp)) hComp hB hgComp
  have hMap : Tendsto (fun y => gA (fwdMapInv W t y))
      (𝓝[H] ((a t).re : ℂ)) (𝓝[H] (((a s).re + W s : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [Chart.loewner, Chart.id, gA, ofReal_add] using
        hTr.add_const (W s : ℂ)
    · refine eventually_nhdsWithin_of_forall fun y hy => ?_
      have hyB := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hy
      exact hgA.1.2.mapsTo ⟨hyB.1, fun hz => hyB.2 (hAB hz)⟩
  have hLim := (hL.tendsto_log_deriv hC hg hG).comp hMap
  have hInherited : Tendsto (fun y => logDerivFwd W t (fwdMapInv W t y) -
      logDerivFwd W s (fwdMapInv W t y)) (𝓝[H] ((a t).re : ℂ))
      (𝓝 (Complex.log (deriv G ((a s).re + W s : ℝ)))) := by
    refine hLim.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    dsimp only [Function.comp_def]
    rw [hEq (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hy), add_sub_cancel_right]
  refine ⟨g, G, ε / 2, hg, hG, him, hpos, hInherited, ?_⟩
  have hLogIm : (Complex.log (deriv G ((a s).re + W s : ℝ))).im = 0 := by
    rw [Complex.log_im, Complex.arg_eq_zero_iff]
    exact ⟨hpos.le, him⟩
  simpa only [Function.comp_def, hLogIm] using
    (Complex.continuous_im.tendsto _).comp hInherited

end InteractingSLE.Theorem14.GW4Fix
