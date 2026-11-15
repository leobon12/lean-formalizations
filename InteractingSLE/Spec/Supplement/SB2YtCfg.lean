/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GAssembleK
import InteractingSLE.Spec.Supplement.SB2YtCusp

/-!
# SB2(1)'s configuration `IsRelConfigJK` when the physical tip is interior

Packet PROVE-T14-SB2DRV (round 13). `FinRel.isRelConfigJK_of_s2_liftOn` needs the relative lift at the line time in
`ℍ` (`γ(s) ∈ ℍ`, i.e. the physical tip off the frontier of the retained set). Only two of its steps used it:

* the cut-time property of the physical tip, which needs only the physical tip in `ℍ` and injectivity
  (**`isCutTime_of_mem_H`**);
* the cusp field, which holds without it (`cusp_of_isSB2RelChain_noTip`).

**`isRelConfigJK_of_s2_liftOn_noTip`**: the configuration with `η(t_L + s) ∈ ℍ` in place of `γ(s) ∈ ℍ`.

Deterministic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv logDerivFwd)

namespace InteractingSLE.Theorem14.SB.FinRel

open Sec7.Lemma71C
open WangWu (chartAL chartAR)
open Supp8.BHMean (jointInv IsSideWord IsFlowedWord)
open Supp8.Q3Chain (flowedData flowedJumps initJumps)

/-- **The physical tip at a line time is a cut time when it is in `ℍ`** (injectivity of the proper curve). -/
theorem isCutTime_of_mem_H {β' : ℝ≥0 → ℂ} (hβ' : Supp9B.IsProperCurve β') {tL : ℝ≥0} {η : ℝ → ℂ} {s : ℝ}
    (hs : 0 ≤ s) (hηβ : ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), η r = β' r.toNNReal) (hηH : η ((tL : ℝ) + s) ∈ H) :
    YuanSimpleApprox.IsCutTime η ((tL : ℝ) + s) := by
  have ht0 : (0 : ℝ) ≤ (tL : ℝ) + s := by have := tL.coe_nonneg; linarith
  have hte : ((tL : ℝ) + s).toNNReal = tL + s.toNNReal := by
    rw [Real.toNNReal_add tL.coe_nonneg hs, Real.toNNReal_coe]
  have htip : η ((tL : ℝ) + s) = β' (tL + s.toNNReal) := by
    rw [hηβ _ ⟨ht0, le_rfl⟩, hte]
  refine ⟨hηH, ?_⟩
  rintro ⟨r, hr, hre⟩
  rw [hηβ r ⟨hr.1, hr.2.le⟩, htip] at hre
  have := hβ'.2.1 hre
  have h2 : ((r.toNNReal : ℝ≥0) : ℝ) = ((tL + s.toNNReal : ℝ≥0) : ℝ) := by rw [this]
  rw [Real.coe_toNNReal _ hr.1, NNReal.coe_add, Real.coe_toNNReal _ hs] at h2
  linarith [hr.2]

/-- **SB2(1)'s configuration `IsRelConfigJK` with the physical tip in `ℍ`** (no interior relative lift needed). -/
theorem isRelConfigJK_of_s2_liftOn_noTip {p : ℝ → ℂ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ Sm : ℝ}
    {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {w : ℝ → ℝ} {η : ℝ → ℂ} {κ χ : ℝ}
    {nL nR nL' nR' : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) (hL : LiftRealOn c)
    (hβ' : Supp9B.IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p '' Icc 0 1 ⊆ Supp9B.closedRightSide β')
    (htL : β' tL = realMin (p '' Icc 0 1)) (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlift : ∀ s, g (γ s) = β' (tL + s))
    (hch : IsSB2RelChain (p '' Icc 0 1) c β' γ tL S₀ Wr ηr) (hS₀S : S₀ < Sm)
    (hnR : interior {r ∈ Ioo (0 : ℝ) Sm | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅)
    {s : ℝ} (hs : s ∈ Ioc 0 S₀)
    (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η)
    (hwt : fwdHull w ((tL : ℝ) + s) = fillH (β' '' Icc 0 (tL + s.toNNReal)))
    (hηβ : ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), η r = β' r.toNNReal) (hηH : η ((tL : ℝ) + s) ∈ H) :
    ∃ (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ), EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH (p '' Icc 0 1)) ∧
      IsRelConfigJK (fillH (p '' Icc 0 1)) c.1 c.2.1 LΨ ∅ w Wr η ηr ((tL : ℝ) + s)
        (capClock (fun r : ℝ => γ r.toNNReal) s) χ (Real.pi / Real.sqrt κ) (forceBoundaryData κ ρL ρR xL xR)
        (flowedData κ ρL' ρR' xL' xR' w ((tL : ℝ) + s))
        (flowedData κ ρL ρR xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (initJumps xL xR)
        (flowedJumps xL' xR' w ((tL : ℝ) + s)) (flowedJumps xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
        G₀ GE G
        (fun z => G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)) -
          χ * ((logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)).im + (LΨ z).im)) := by
  have hch' := hch
  obtain ⟨hWr, hWr0, hηr, hc0, hcm, -, hKK⟩ := hch'
  have hsI : s ∈ Icc 0 S₀ := ⟨hs.1.le, hs.2⟩
  obtain ⟨hu0, -, -, hIn, -⟩ := hKK s hsI
  have hupos : 0 < capClock (fun r : ℝ => γ r.toNNReal) s := by
    have := hcm ⟨le_rfl, hs.1.le.trans hs.2⟩ hsI hs.1
    rwa [hc0] at this
  obtain ⟨G₀, G, hG₀, hG, hsu, hfl⟩ := exists_relWordData κ ρL ρR hxL hxR hηr hWr hWr0 hupos
  have ht0 : (0 : ℝ) ≤ (tL : ℝ) + s := by have := tL.coe_nonneg; linarith [hs.1]
  obtain ⟨GE, hGE, hsE⟩ := exists_explWordData κ ρL' ρR' hxL' hxR' hη hw hw0 ht0
  have hcut := isCutTime_of_mem_H hβ' hs.1.le hηβ hηH
  have hηt : η ((tL : ℝ) + s) = β' (tL + s.toNNReal) := by
    rw [hηβ _ ⟨ht0, le_rfl⟩, Real.toNNReal_add tL.coe_nonneg hs.1.le, Real.toNNReal_coe]
  have hIn' : ∀ z ∈ fwdHull w ((tL : ℝ) + s), z ∉ fillH (p '' Icc 0 1) →
      c.1 z ∈ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s) := by
    rw [hwt]; exact hIn
  obtain ⟨LΨ, hLeq, hcfg⟩ := isRelConfigJK_of_s2 (χ := χ) hp hp0 hc hgc hgi
    (fun y _ hy => hliftR_of_liftRealOn hc.1 hL y hy) hβ' hγ hlift hch hS₀S hnR hs hw hw0 hη hwt hηt hcut
    (cusp_of_isSB2RelChain_noTip hp hp0 hpH hc hgc hgi hβ' hβ'0 hA htL hγ hγ0 hlift hch hs hwt)
    (fun x hx => eventually_freeNearK_of_notMem_closure hc.1 hgc hgi hgf hWr hWr0 hηr hu0 hIn' hx)
    hG₀ hGE hG hsE hsu hfl
  exact ⟨LΨ, G₀, GE, G, hLeq, hcfg⟩

end InteractingSLE.Theorem14.SB.FinRel
