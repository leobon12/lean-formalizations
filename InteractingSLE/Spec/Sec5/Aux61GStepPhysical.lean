/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GStepSeed

/-! # The actual physical own mean has the reference seed germ

The free current collar supplies the coordinate reflection. R1 and the
landed two-side theorem supply the inherited relative phase with value zero.
No seed-coordinate derivative, seed phase limit or mean formula is assumed.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology
open QuantumZipper (H chiC fwdHull fwdMap fwdMapInv logDerivFwd)

namespace InteractingSLE.Sec5.Aux61GStep
open Aux61Restart Aux61TwoS
open Aux61Fib (FibData)

/-- Freeze a finite simple interior prefix to apply the existing proper-arc
phase theorem. No condition on the physical trace after the prefix is used. -/
theorem tendsto_relative_phase_of_prefix {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (hr : 0 < r)
    (hinj : InjOn η (Icc 0 r)) (hH : ∀ u ∈ Ioc 0 r, η u ∈ H)
    {D : Set ℂ} (hDO : D ⊆ H \ fwdHull W r)
    (hB : IsHPHull (stripTargetHull D))
    (hcollar : ∃ δ > 0, MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) D) :
    Tendsto (fun z => (physicalRestartLog (stripTargetHull D) (fwdMapInv W r z) -
      logDerivFwd W r (fwdMapInv W r z)).im) (𝓝[H] 0) (𝓝 0) := by
  have hLT := WangWu.isLoewnerTraceLT_of_isLoewnerTrace hη (r + 1)
  have hηe := hLT.isLoewnerTrace_ext hW hW0 hr.le (by linarith)
  have hηep := WangWu.isProperArc_extTrace hLT hW hW0 hr.le (by linarith) hinj hH
  have hWe : Continuous (YuanCorollary13.extDrive W r) := YuanCorollary13.continuous_extDrive hW
  have hWe0 := YuanCorollary13.extDrive_zero hW0 hr.le
  have heq : ∀ s ∈ Icc (0 : ℝ) r, YuanCorollary13.extDrive W r s = W s :=
    fun s hs => YuanCorollary13.extDrive_eq hs.2
  have hK := YuanCorollary13.fwdHull_eq_of_eqOn_Icc hWe hW hr.le heq
  have hF : ∀ z ∈ H, fwdMapInv (YuanCorollary13.extDrive W r) r z = fwdMapInv W r z :=
    fun z hz => ZhanGT4.fwdMapInv_congr hWe hW hWe0 hW0 hr.le heq hz
  have hL : ∀ z, logDerivFwd (YuanCorollary13.extDrive W r) r z = logDerivFwd W r z :=
    fun z => Ito.logDerivFwd_congr_of_eqOn (T := r) heq hr.le le_rfl
  have hDOe : D ⊆ H \ fwdHull (YuanCorollary13.extDrive W r) r := by rw [hK]; exact hDO
  obtain ⟨δ, hδ, hcol⟩ := hcollar
  have hcole : ∃ δ > 0, MapsTo (fwdMapInv (YuanCorollary13.extDrive W r) r) (ball 0 δ ∩ H) D :=
    ⟨δ, hδ, fun z hz => by rw [hF z hz.2]; exact hcol hz⟩
  have ht := tendsto_im_physicalRestartLog_retained_sub_logDerivFwd hWe hWe0 hηe hηep hr hDOe hB hcole
  refine ht.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  rw [hF z hz, hL]

/-- The charted physical coupling mean agrees with the chosen canonical
reference mean at the seed itself. The lift is the actual inherited R1 lift. -/
theorem tendsto_charted_couplingMean_sub_refMean0_seed
    (d : FibData) (F : Impl.ForceWord) (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ)
    (hL : ∀ i, vL i < 0 ∨ F.ρL i = 0) (hR : ∀ j, 0 < vR j ∨ F.ρR j = 0)
    (hleft_height : PiecewiseConstantBoundaryData.leftLim d.bR 0 = -sleLambda d.κ)
    (hright_height : PiecewiseConstantBoundaryData.rightLim d.bR 0 = sleLambda d.κ)
    {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η)
    (hr : 0 < r) (hηinj : InjOn η (Icc 0 r)) (hηH : ∀ u ∈ Ioc 0 r, η u ∈ H)
    {c : Chart} (hc : c.IsConformal) (hsub : (c.dom : Set ℂ) ⊆ H \ fwdHull W r)
    (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
    (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)
    (hcollar : ∃ δ > 0, MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) c.dom)
    (hzero : Tendsto (c.1 ∘ fwdMapInv W r) (𝓝[H] 0) (𝓝 0))
    (hlift : ∀ z ∈ c.dom, c.2.2 z = (physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) z).im) :
    Tendsto (fun z => couplingMean d.κ W r (Impl.forceExt d.κ F vL vR) (c.2.1 z) +
      chiC d.κ * c.2.2 (c.2.1 z) - Aux61GlueK.refMean0 d z) (𝓝[H] 0) (𝓝 0) := by
  obtain ⟨ε, -, G, hG, hG0, hcol⟩ :=
    exists_posReflect_seed_transition hW hW0 hη (hηH r ⟨hr, le_rfl⟩) hr hc hsub hB hscale hcollar hzero
  let Θ : ℂ → ℂ := fwdMap W r ∘ c.2.1
  have hleft : ∀ w ∈ H ∩ ball ((0 : ℝ) : ℂ) ε,
      Θ ((c.1 ∘ fwdMapInv W r) w) = w := by
    intro w hw
    dsimp only [Θ, Function.comp_apply]
    rw [hc.inv_fwd (hcol hw)]
    exact QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hr.le hw.1
  have hright : ∀ z ∈ H, (c.1 ∘ fwdMapInv W r) (Θ z) = z := by
    intro z hz
    dsimp only [Θ, Function.comp_apply]
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr.le (hsub (hc.inv_mem_dom hz))]
    exact hc.2.2 z hz
  have hΘ : Tendsto Θ (𝓝[H] 0) (𝓝[H] 0) := by
    have ht := hG.tendsto_leftInv hleft
    simpa only [hG0, ofReal_zero] using ht
  have hphase : Tendsto (fun z => c.2.2 (c.2.1 z) - (logDerivFwd W r (c.2.1 z)).im)
      (𝓝[H] 0) (𝓝 0) := by
    have ht := (tendsto_relative_phase_of_prefix
      hW hW0 hη hr hηinj hηH hsub hB hcollar).comp hΘ
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    dsimp only [Function.comp_apply, Θ]
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr.le (hsub (hc.inv_mem_dom hz)),
      sub_im, hlift _ (hc.inv_mem_dom hz)]
  have ht := tendsto_forceMean_inverse_sub_reference_seed d F vL vR hL hR
    hleft_height hright_height hG hG0 hleft hright hphase
  convert ht using 1
  funext z
  dsimp only [Θ, Function.comp_apply, couplingMean]
  ring

end InteractingSLE.Sec5.Aux61GStep
