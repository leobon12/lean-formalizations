/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaTime
import InteractingSLE.Spec.ZhanGT4.A1G3L2Zero

/-! # GW4: exposed landings belong to the closed ambient hull -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.PocketStopSide Sec7.R5Lift MartChar.RealFlow

/-- The closed-hull form of R.5's exposed-landing argument. It includes
original-real landings: a ball avoiding the closed ambient hull pulls back
to an alive original real point, whose image cannot be between the seeds. -/
theorem landing_mem_closure_hull_of_seed {c : Chart} (hc : c.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {Q : ℝ} (hQ : 0 < Q)
    {E Fb : ℂ → ℂ} (hE : EqOn E c.2.1 H) (hEc : ContinuousOn E Hbar)
    (hFb : EqOn Fb (fwdMapInv W Q) H) (hFbc : ContinuousOn Fb Hbar)
    {K : Set ℂ} (hdom : ((c.loewner W Q).dom : Set ℂ) = (c.dom : Set ℂ) ∩ (H \ K))
    {ξ : ℝ} (hξ : ξ ∈ Ioo (-rightImg (fun r => -W r) 0 Q - W Q) (rightImg W 0 Q - W Q))
    {p : ℂ} (hland : Tendsto (c.loewner W Q).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) :
    p ∈ closure K := by
  have hNow := hc.loewner hW hW0 hQ.le
  have := nhdsWithin_H_neBot ξ
  have hξbar : (ξ : ℂ) ∈ Hbar := ofReal_mem_Hbar ξ
  let b := Fb ξ
  have hbT : Tendsto (fwdMapInv W Q) (𝓝[H] (ξ : ℂ)) (𝓝 b) :=
    ((hFbc _ hξbar).tendsto.mono_left (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)).congr'
      (eventually_nhdsWithin_of_forall fun y hy => hFb hy)
  have hinvH : ∀ y ∈ H, fwdMapInv W Q y ∈ H := fun y hy =>
    QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hQ.le hy
  have hbbar : b ∈ Hbar := by
    rw [← show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
    exact mem_closure_of_tendsto hbT (eventually_nhdsWithin_of_forall hinvH)
  have hpE : p = E b := by
    have h := (hEc b hbbar).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hbT, eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.H_subset_Hbar (hinvH y hy)⟩)
    exact tendsto_nhds_unique hland (h.congr' (eventually_nhdsWithin_of_forall fun y hy => hE (hinvH y hy)))
  by_contra hpK
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p hpK
  have hpdom := landing_notMem_dom hNow hland
  have hbim : b.im = 0 := by
    by_contra hne
    have hbH : b ∈ H := lt_of_le_of_ne hbbar (Ne.symm hne)
    apply hpdom
    rw [hdom, hpE, hE hbH]
    exact ⟨hc.inv_mem_dom hbH, hc.2.1 hbH, fun h => hpK (hpE ▸ hE hbH ▸ subset_closure h)⟩
  obtain ⟨δ, hδ, hδE⟩ : ∃ δ > 0, ∀ z ∈ Hbar ∩ ball b δ, E z ∈ ball p ε := by
    have hmem := (hEc b hbbar).preimage_mem_nhdsWithin
      (isOpen_ball.mem_nhds (by rw [← hpE]; exact mem_ball_self hε))
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hmem
    exact ⟨δ, hδ, fun z hz => hsub ⟨hz.2, hz.1⟩⟩
  have hdisj : Disjoint (ball b δ) (fwdHull W Q) := by
    refine Set.disjoint_left.2 fun z hzb hzK => ?_
    have hzH : z ∈ H := hzK.1
    have hEz := hδE z ⟨QuantumZipper.H_subset_Hbar hzH, hzb⟩
    rw [hE hzH] at hEz
    have hzC : c.2.1 z ∈ ((c.loewner W Q).dom : Set ℂ) := by
      rw [hdom]
      exact ⟨hc.inv_mem_dom hzH, hc.2.1 hzH, fun h => hball hEz (subset_closure h)⟩
    rw [hNow.coe_dom] at hzC
    obtain ⟨v, hvH, hv⟩ := hzC
    have hv' : c.2.1 (fwdMapInv W Q v) = c.2.1 z := hv
    have hzv := hc.injOn (hinvH v hvH) hzH hv'
    exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hQ.le hvH).2 (hzv ▸ hzK)
  have hbr : b = (b.re : ℂ) := Complex.ext (by simp only [ofReal_re]) (by simp only [ofReal_im, hbim])
  have hb0 : b.re ≠ 0 := by
    intro h0
    have hbzero : b = 0 := by rw [hbr, h0, ofReal_zero]
    obtain ⟨z, hzK, hz⟩ := Metric.mem_closure_iff.1
      (ConformalImageFull.zero_mem_closure_fwdHull hW hW0 hQ) δ hδ
    exact Set.disjoint_left.1 hdisj (by simpa only [hbzero, mem_ball, dist_comm] using hz) hzK
  obtain ⟨a, ha⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 hb0 hQ.le hδ (hbr ▸ hdisj)
  have hcont := ZhanGT4.A1G3L2.continuousAt_fwdMap_of_isForwardSol
    (show Q < Q + 1 by linarith) hQ.le hW.continuousOn ha
  have hval : (ξ : ℂ) = fwdMap W Q (b.re : ℂ) := by
    have h := hcont.tendsto.comp (hbr ▸ hbT)
    have hId : Tendsto (fun y : ℂ => y) (𝓝[H] (ξ : ℂ)) (𝓝 (fwdMap W Q (b.re : ℂ))) :=
      h.congr' (eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hQ.le hy)
    exact tendsto_nhds_unique (tendsto_id.mono_left nhdsWithin_le_nhds) hId
  have hξre : ξ = (fwdMap W Q (b.re : ℂ)).re := by rw [← hval, ofReal_re]
  rcases lt_or_gt_of_ne hb0 with hneg | hpos
  · exact (not_le_of_gt hξ.1) (hξre ▸ WangWu.re_fwdMap_le_neg_rightImg hW hW0 hQ.le hneg ha)
  · exact (not_le_of_gt hξ.2) (hξre ▸ WangWu.rightImg_sub_le_re_fwdMap hW hW0 hQ.le hpos ha)

end InteractingSLE.Theorem14.GW4Fix
