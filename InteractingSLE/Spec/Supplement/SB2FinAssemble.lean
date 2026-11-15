/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinTip
import InteractingSLE.Spec.Supplement.SB2FinUnionC
import InteractingSLE.Spec.Supplement.SB2FinFinK

/-!
# SB2(1)'s deterministic configuration, assembled

Packet PROVE-T14-SB2FIN. The cusp configuration `IsRelConfigJC` (ruling R84) for SB2(1)'s actual geometry, from the
pieces proved in this packet:

* `chart` from `exists_isRetainedChartOff` (`SB2FinChart`), given the chart lift's boundary value `0` at the free real
  points (`hliftR`; left of `L` it is `IsLeftEntryChart`'s own clause);
* `hw hw0 hη ht`: the physical chain (`exists_globalTrace_of_isGeneratingTrace`), as hypotheses with the hull identity
  `fwdHull w t = fill β'([0, t])` at `t = t_L + s`;
* `hWr hWr0 hηr hu hullIn hullFr` from `IsSB2RelChain` (`SB2FinConfig`), `bad` vacuous (`Sb = ∅`);
* `tip` from `tip_of_isCutTime` at a fresh physical tip (`SB2FinTip`);
* `collar` from `collar_of_isSB2RelChain` (`SB2FinCollar`), `landK` from `landK_of_isSB2RelChain` (`SB2FinLand`);
* `cusp`, `finK` and the word data as the remaining named hypotheses.

**`isRelConfigJC_of_s2`** is a conditional assembly with a distinct name; it replaces no source theorem.
`isRelConfigJC_of_s2_pinch`: the same with `finK` derived from finitely many pinch points of the retained chart
(`finK_of_finite_pinch`).
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

/-- **SB2(1)'s cusp configuration from S2's geometry** (conditional assembly): for the retained path `A = p([0, 1])`,
its left entry chart `c` with the boundary extension `g`, the S1 witness `β'` with the S2 lift `γ`, the relative chain
`(Wr, ηr)` of `γ` (`IsSB2RelChain`, with no open real arc of the witness on `(0, S)`), and a physical chain `(w, η)`
whose hull at `t = t_L + s` is `fill β'([0, t])` and whose tip there is fresh and equal to `β'(t)`: given the chart
lift's boundary values (`hliftR`), the `cusp` and `finK` finiteness and the word data, the cusp configuration holds
at the physical time `t_L + s` and the relative time `a s`, `0 < s ≤ S₀`, for the filled retained set `fill A`, with a
derivative logarithm `LΨ` of the chart (`c.lift = Im LΨ` on `D_A`) and the candidate `v` built from it. -/
theorem isRelConfigJC_of_s2 {p : ℝ → ℂ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ Sm : ℝ}
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
    (hfinK : {x : ℝ | extendFrom H (fwdMapInv Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ) ∉
        closure (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) ∧
      extendFrom H (jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ) ∈
        closure (fwdHull w ((tL : ℝ) + s) \ fillH (p '' Icc 0 1))}.Finite)
    (hbhe₀ : IsBoundedHarmonicExtension β₀ J₀ G₀) (hbheE : IsBoundedHarmonicExtension βE JE GE)
    (hbheu : IsBoundedHarmonicExtension βu Ju G)
    (hsideE : IsSideWord βE JE (fwdMapInv w ((tL : ℝ) + s)) (fwdHull w ((tL : ℝ) + s)) lam)
    (hsideu : IsSideWord βu Ju (fwdMapInv Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
      (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) lam)
    (hflow : IsFlowedWord βu β₀ Ju J₀ (fwdMapInv Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
      (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s))) :
    ∃ LΨ : ℂ → ℂ, EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH (p '' Icc 0 1)) ∧
      IsRelConfigJC (fillH (p '' Icc 0 1)) c.1 c.2.1 LΨ ∅ w Wr η ηr ((tL : ℝ) + s)
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
    (Finset.notMem_empty b), ?_, ⟨x₁, hx₁, hgood, hleft, ?_⟩, ?_, hcusp, hfinK, hbhe₀, hbheE, hbheu, hsideE,
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

/-- **SB2(1)'s cusp configuration with `finK` from the pinch points** (`isRelConfigJC_of_s2` with `hfinK` replaced by
finitely many real points at which `g` is not injective on `ℝ`). -/
theorem isRelConfigJC_of_s2_pinch {p : ℝ → ℂ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ Sm : ℝ}
    {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {w : ℝ → ℝ} {η : ℝ → ℂ} {χ lam : ℝ}
    {β₀ βE βu : ℝ → ℝ} {J₀ JE Ju : Finset ℝ} {G₀ GE G : ℂ → ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H)
    (hliftR : ∀ y : ℝ, y ≠ 0 → (y : ℂ) ∉ closure (fillH (p '' Icc 0 1)) →
      Tendsto c.2.2 (𝓝[H \ fillH (p '' Icc 0 1)] (y : ℂ)) (𝓝 0))
    (hpinch : {v : ℝ | ∃ v' : ℝ, v' ≠ v ∧ g v' = g v}.Finite)
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
    (hbhe₀ : IsBoundedHarmonicExtension β₀ J₀ G₀) (hbheE : IsBoundedHarmonicExtension βE JE GE)
    (hbheu : IsBoundedHarmonicExtension βu Ju G)
    (hsideE : IsSideWord βE JE (fwdMapInv w ((tL : ℝ) + s)) (fwdHull w ((tL : ℝ) + s)) lam)
    (hsideu : IsSideWord βu Ju (fwdMapInv Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
      (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) lam)
    (hflow : IsFlowedWord βu β₀ Ju J₀ (fwdMapInv Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
      (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s))) :
    ∃ LΨ : ℂ → ℂ, EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH (p '' Icc 0 1)) ∧
      IsRelConfigJC (fillH (p '' Icc 0 1)) c.1 c.2.1 LΨ ∅ w Wr η ηr ((tL : ℝ) + s)
      (capClock (fun r : ℝ => γ r.toNNReal) s) χ lam β₀ βE βu J₀ JE Ju G₀ GE G
      (fun z => G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)) -
        χ * ((logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)).im + (LΨ z).im)) := by
  have hAc : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  have hApc : IsPreconnected (p '' Icc 0 1 ∪ {z : ℂ | z.im ≤ 0}) :=
    (isPreconnected_Icc.image p hp).union 0 ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩ (show (0 : ℂ).im ≤ 0 by simp)
      isPreconnected_lowerHalf
  have hch' := hch
  obtain ⟨hWr, hWr0, hηr, hc0, hcm, -, hK⟩ := hch'
  have hsI : s ∈ Icc 0 S₀ := ⟨hs.1.le, hs.2⟩
  obtain ⟨-, -, -, hIn, -⟩ := hK s hsI
  have hupos : 0 < capClock (fun r : ℝ => γ r.toNNReal) s := by
    have := hcm ⟨le_rfl, hs.1.le.trans hs.2⟩ hsI hs.1
    rwa [hc0] at this
  have hKin : ∀ z ∈ fwdHull w ((tL : ℝ) + s), z ∉ fillH (p '' Icc 0 1) →
      c.1 z ∈ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s) := by
    rw [hwt]; exact hIn
  exact isRelConfigJC_of_s2 hp hp0 hc hgc hgi hliftR hβ' hγ hlift hch hS₀S hnR hs hw hw0 hη hwt hηt hcut hcusp
    (finK_of_finite_pinch hAc.isBounded hApc hc hgc hgi hWr hWr0 hηr hupos hKin hpinch) hbhe₀ hbheE hbheu hsideE
    hsideu hflow

end InteractingSLE.Theorem14.SB.FinRel
