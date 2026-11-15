/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GUnionK
import InteractingSLE.Spec.Supplement.SB2GPinch

/-!
# SB2(1)'s configuration `IsRelConfigJK`, assembled without `hpinch`

Packet PROVE-T14-SB2FIN2. `IsRelConfigJK` (`SB2GUnionK`: `IsRelConfigJC` with `finK` replaced by the one-sided
condition `oneK`) for SB2(1)'s geometry:

* `isRelConfigJK_of_s2`: `isRelConfigJC_of_s2` with `hfinK` replaced by `honeK`;
* **`isRelConfigJK_of_s2_liftOn`**: the configuration from S1/S2's data, the physical chain with its fresh tip, the
  force words, finite fibres of `g` (`Lv.finite_fibre_of_isLeftEntryChart`) and `LiftRealOn c` (the run chart,
  `liftRealOn_runChart`) — `cusp` by `cusp_of_isSB2RelChain`, `oneK` by `eventually_freeNearK_of_notMem_closure`,
  `hliftR` by `hliftR_of_liftRealOn`. No `hpinch`.

Conditional assembly with distinct names; it replaces no source theorem.
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

/-- **SB2(1)'s configuration `IsRelConfigJK` from S2's geometry** (`isRelConfigJC_of_s2` with `hfinK` replaced by
the one-sided condition `honeK`; conditional assembly with a distinct name). -/
theorem isRelConfigJK_of_s2 {p : ℝ → ℂ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ Sm : ℝ}
    {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {w : ℝ → ℝ} {η : ℝ → ℂ} {χ lam : ℝ}
    {β₀ βE βu : ℝ → ℝ} {J₀ JE Ju : Finset ℝ} {G₀ GE G : ℂ → ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H)
    (hliftR : ∀ y : ℝ, y ≠ 0 → (y : ℂ) ∉ closure (fillH (p '' Icc 0 1)) →
      Tendsto c.2.2 (𝓝[H \ fillH (p '' Icc 0 1)] (y : ℂ)) (𝓝 0))
    (hβ' : Supp9B.IsProperCurve β') (hγ : Supp9B.IsProperCurve γ) (hlift : ∀ s, g (γ s) = β' (tL + s))
    (hch : IsSB2RelChain (p '' Icc 0 1) c β' γ tL S₀ Wr ηr) (hS₀S : S₀ < Sm)
    (hnR : interior {r ∈ Ioo (0 : ℝ) Sm | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅)
    {s : ℝ} (hs : s ∈ Ioc 0 S₀)
    (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η)
    (hwt : fwdHull w ((tL : ℝ) + s) = fillH (β' '' Icc 0 (tL + s.toNNReal)))
    (hηt : η ((tL : ℝ) + s) = β' (tL + s.toNNReal)) (hcut : YuanSimpleApprox.IsCutTime η ((tL : ℝ) + s))
    (hcusp : {x : ℝ | x ∈ Ico (chartAL Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
        (chartAR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) ∧
      extendFrom H (jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ) ∈
        closure (fillH (p '' Icc 0 1)) ∧
      ¬ ∃ r > 0, ∀ᶠ y in 𝓝[H] (x : ℂ), jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s) y ∈
        freeNear (fillH (p '' Icc 0 1)) (fwdHull w ((tL : ℝ) + s))
          (extendFrom H (jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ)) r}.Finite)
    (honeK : ∀ x : ℝ, extendFrom H (fwdMapInv Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ) ∉
        closure (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) → ∃ r > 0, ∀ᶠ y in 𝓝[H] (x : ℂ),
        jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s) y ∈ freeNear (fwdHull w ((tL : ℝ) + s))
          (fillH (p '' Icc 0 1))
          (extendFrom H (jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ)) r)
    (hbhe₀ : IsBoundedHarmonicExtension β₀ J₀ G₀) (hbheE : IsBoundedHarmonicExtension βE JE GE)
    (hbheu : IsBoundedHarmonicExtension βu Ju G)
    (hsideE : IsSideWord βE JE (fwdMapInv w ((tL : ℝ) + s)) (fwdHull w ((tL : ℝ) + s)) lam)
    (hsideu : IsSideWord βu Ju (fwdMapInv Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
      (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) lam)
    (hflow : IsFlowedWord βu β₀ Ju J₀ (fwdMapInv Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
      (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s))) :
    ∃ LΨ : ℂ → ℂ, EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH (p '' Icc 0 1)) ∧
      IsRelConfigJK (fillH (p '' Icc 0 1)) c.1 c.2.1 LΨ ∅ w Wr η ηr ((tL : ℝ) + s)
      (capClock (fun r : ℝ => γ r.toNNReal) s) χ lam β₀ βE βu J₀ JE Ju G₀ GE G
      (fun z => G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)) -
        χ * ((logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)).im + (LΨ z).im)) := by
  have hAc : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  have hAb := hAc.isBounded
  have hApc : IsPreconnected (p '' Icc 0 1 ∪ {z : ℂ | z.im ≤ 0}) :=
    (isPreconnected_Icc.image p hp).union 0 ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩ (show (0 : ℂ).im ≤ 0 by simp)
      isPreconnected_lowerHalf
  obtain ⟨LΨ, hchart, hLeq⟩ := exists_isRetainedChartOff hAb hApc hc hgc hgi hliftR
  have hch' := hch
  obtain ⟨hWr, hWr0, hηr, -, -, -, hK⟩ := hch'
  have hsI : s ∈ Icc 0 S₀ := ⟨hs.1.le, hs.2⟩
  obtain ⟨hu, -, -, hIn, hFr⟩ := hK s hsI
  have ht : (0 : ℝ) < (tL : ℝ) + s := by have := tL.coe_nonneg; linarith [hs.1]
  have hKin : ∀ z ∈ fwdHull w ((tL : ℝ) + s), z ∉ fillH (p '' Icc 0 1) →
      c.1 z ∈ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s) := by
    rw [hwt]; exact hIn
  have hland := extendFrom_jointInv_zero_of_isSB2RelChain hgc hgi hlift hch hsI
  rw [← hηt] at hland
  obtain ⟨x₁, hx₁, hgood, hleft, hx₀⟩ := collar_of_isSB2RelChain hp hp0 hc hgc hgi hch hsI
  refine ⟨LΨ, hLeq, ⟨hchart, hw, hw0, hη, ht.le, hWr, hWr0, hηr, hu, hKin, ?_, fun b hb => absurd hb
    (Finset.notMem_empty b), ?_, ⟨x₁, hx₁, hgood, hleft, ?_⟩, ?_, hcusp, honeK, hbhe₀, hbheE, hbheu, hsideE,
    hsideu, hflow, fun z => rfl⟩⟩
  · intro z hz hfr
    rw [hwt]
    exact hFr z hz hfr
  · exact tip_of_isCutTime hchart hw hw0 hη ht hWr hWr0 hηr hu hKin (fun b hb => absurd hb (Finset.notMem_empty b))
      hcut hland
  · rw [hwt]; exact hx₀
  · intro x hx
    rw [hwt]
    exact landK_of_isSB2RelChain hgc hgi hβ' hγ hlift hch hS₀S hnR hs x hx

/-- **SB2(1)'s configuration `IsRelConfigJK` without `hpinch`** (conditional assembly). -/
theorem isRelConfigJK_of_s2_liftOn {p : ℝ → ℂ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ Sm : ℝ}
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
    (hηβ : ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), η r = β' r.toNNReal) (hγH : γ s.toNNReal ∈ H) :
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
  have hcut := isCutTime_of_lift_mem_H hc.1 hgi hβ' hlift hs.1.le hηβ hγH
  have hηt : η ((tL : ℝ) + s) = β' (tL + s.toNNReal) := by
    rw [hηβ _ ⟨ht0, le_rfl⟩, Real.toNNReal_add tL.coe_nonneg hs.1.le, Real.toNNReal_coe]
  have hIn' : ∀ z ∈ fwdHull w ((tL : ℝ) + s), z ∉ fillH (p '' Icc 0 1) →
      c.1 z ∈ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s) := by
    rw [hwt]; exact hIn
  obtain ⟨LΨ, hLeq, hcfg⟩ := isRelConfigJK_of_s2 (χ := χ) hp hp0 hc hgc hgi
    (fun y _ hy => hliftR_of_liftRealOn hc.1 hL y hy) hβ' hγ hlift hch hS₀S hnR hs hw hw0 hη hwt hηt hcut
    (cusp_of_isSB2RelChain hp hp0 hpH hc hgc hgi hβ' hβ'0 hA htL hγ hγ0 hlift hch hs hγH hwt)
    (fun x hx => eventually_freeNearK_of_notMem_closure hc.1 hgc hgi hgf hWr hWr0 hηr hu0 hIn' hx)
    hG₀ hGE hG hsE hsu hfl
  exact ⟨LΨ, G₀, GE, G, hLeq, hcfg⟩

end InteractingSLE.Theorem14.SB.FinRel
