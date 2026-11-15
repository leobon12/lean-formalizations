/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinAssemble
import InteractingSLE.Spec.Supplement.Q3ChainWord
import InteractingSLE.Spec.Sec4.Special3Thin

/-!
# SB2(1)'s word data from force words

Packet PROVE-T14-SB2FIN. The word fields `bhe₀ bheE bheu sideE sideu flow` of `IsRelConfigJC` for force words: the
retained word is the force data `β₀` of a force word `(xL, xR, ρL, ρR)` (the relative flow line's word in the launch
chart), the relative word is the same force data read at the marks flowed by the relative driver up to the relative
time (`Supp8.Q3Chain.flowedData`), with the flow-line side heights `±π/√κ` on the relative hull image; the explored word
is the physical flow line's own force data flowed by its driver. The bounded harmonic extensions exist
(`Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData`); the side and flowed words are the landed
`Supp8.Q3Chain.isSideWord_flowedData`, `isFlowedWord_flowedData`.

* `exists_relWordData`, `exists_explWordData`;
* **`isRelConfigJC_of_s2_force`**: `isRelConfigJC_of_s2_pinch` with the word data supplied by force words.
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

/-- **The retained and relative word data of a force word.** -/
theorem exists_relWordData (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {Wr : ℝ → ℝ} {ηr : ℝ → ℂ}
    (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) {u : ℝ} (hu : 0 < u) :
    ∃ G₀ G : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (initJumps xL xR) G₀ ∧
      IsBoundedHarmonicExtension (flowedData κ ρL ρR xL xR Wr u) (flowedJumps xL xR Wr u) G ∧
      IsSideWord (flowedData κ ρL ρR xL xR Wr u) (flowedJumps xL xR Wr u) (fwdMapInv Wr u) (fwdHull Wr u)
        (Real.pi / Real.sqrt κ) ∧
      IsFlowedWord (flowedData κ ρL ρR xL xR Wr u) (forceBoundaryData κ ρL ρR xL xR) (flowedJumps xL xR Wr u)
        (initJumps xL xR) (fwdMapInv Wr u) (fwdHull Wr u) := by
  obtain ⟨G₀, hG₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR xL xR
  obtain ⟨G, hG⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
    (fun i => Exist.StagedLaw.markPosL Wr u (xL i)) (fun j => Exist.StagedLaw.markPos Wr u (xR j))
  refine ⟨G₀, G, ?_, ?_, Supp8.Q3Chain.isSideWord_flowedData hηr hWr hWr0 hu.le κ ρL ρR hxL hxR,
    Supp8.Q3Chain.isFlowedWord_flowedData hηr hWr hWr0 hu κ ρL ρR hxL hxR⟩
  · rw [Supp8.Q3Chain.coe_initJumps]; exact hG₀
  · rw [flowedJumps, Supp8.Q3Chain.coe_initJumps]; exact hG

/-- **The explored word data of a force word** (the physical flow line's own word flowed by its driver). -/
theorem exists_explWordData (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {w : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace w η) (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ GE : ℂ → ℝ, IsBoundedHarmonicExtension (flowedData κ ρL ρR xL xR w t) (flowedJumps xL xR w t) GE ∧
      IsSideWord (flowedData κ ρL ρR xL xR w t) (flowedJumps xL xR w t) (fwdMapInv w t) (fwdHull w t)
        (Real.pi / Real.sqrt κ) := by
  obtain ⟨GE, hGE⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
    (fun i => Exist.StagedLaw.markPosL w t (xL i)) (fun j => Exist.StagedLaw.markPos w t (xR j))
  refine ⟨GE, ?_, Supp8.Q3Chain.isSideWord_flowedData hη hw hw0 ht κ ρL ρR hxL hxR⟩
  rw [flowedJumps, Supp8.Q3Chain.coe_initJumps]; exact hGE

/-- **SB2(1)'s cusp configuration with force-word data** (`isRelConfigJC_of_s2_pinch` with the word fields supplied by
force words — the retained/relative word `(xL, xR, ρL, ρR)` and the explored word `(xL', xR', ρL', ρR')`, side height
`π/√κ` — and the fresh tip supplied by `isCutTime_of_lift_mem_H` from the physical trace being the witness on
`[0, t_L + s]` and the lift point `γ s` lying in `ℍ`). Remaining named inputs: `hliftR`, `hpinch`, `hcusp`, `hγH`, and
the physical chain's hull identity `hwt`. -/
theorem isRelConfigJC_of_s2_force {p : ℝ → ℂ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ Sm : ℝ}
    {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {w : ℝ → ℝ} {η : ℝ → ℂ} {κ χ : ℝ}
    {nL nR nL' nR' : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
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
    (hηβ : ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), η r = β' r.toNNReal) (hγH : γ s.toNNReal ∈ H)
    (hcusp : {x : ℝ | x ∈ Ico (chartAL Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
        (chartAR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) ∧
      extendFrom H (jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ) ∈
        closure (fillH (p '' Icc 0 1)) ∧
      ¬ ∃ r > 0, ∀ᶠ y in 𝓝[H] (x : ℂ), jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s) y ∈
        freeNear (fillH (p '' Icc 0 1)) (fwdHull w ((tL : ℝ) + s))
          (extendFrom H (jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ)) r}.Finite) :
    ∃ (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ), EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH (p '' Icc 0 1)) ∧
      IsRelConfigJC (fillH (p '' Icc 0 1)) c.1 c.2.1 LΨ ∅ w Wr η ηr ((tL : ℝ) + s)
        (capClock (fun r : ℝ => γ r.toNNReal) s) χ (Real.pi / Real.sqrt κ) (forceBoundaryData κ ρL ρR xL xR)
        (flowedData κ ρL' ρR' xL' xR' w ((tL : ℝ) + s))
        (flowedData κ ρL ρR xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (initJumps xL xR)
        (flowedJumps xL' xR' w ((tL : ℝ) + s)) (flowedJumps xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
        G₀ GE G
        (fun z => G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)) -
          χ * ((logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)).im + (LΨ z).im)) := by
  have hch' := hch
  obtain ⟨hWr, hWr0, hηr, hc0, hcm, -, -⟩ := hch'
  have hsI : s ∈ Icc 0 S₀ := ⟨hs.1.le, hs.2⟩
  have hupos : 0 < capClock (fun r : ℝ => γ r.toNNReal) s := by
    have := hcm ⟨le_rfl, hs.1.le.trans hs.2⟩ hsI hs.1
    rwa [hc0] at this
  obtain ⟨G₀, G, hG₀, hG, hsu, hfl⟩ := exists_relWordData κ ρL ρR hxL hxR hηr hWr hWr0 hupos
  have ht0 : (0 : ℝ) ≤ (tL : ℝ) + s := by have := tL.coe_nonneg; linarith [hs.1]
  obtain ⟨GE, hGE, hsE⟩ := exists_explWordData κ ρL' ρR' hxL' hxR' hη hw hw0 ht0
  have hcut := isCutTime_of_lift_mem_H hc.1 hgi hβ' hlift hs.1.le hηβ hγH
  have hηt : η ((tL : ℝ) + s) = β' (tL + s.toNNReal) := by
    rw [hηβ _ ⟨ht0, le_rfl⟩, Real.toNNReal_add tL.coe_nonneg hs.1.le, Real.toNNReal_coe]
  obtain ⟨LΨ, hLeq, hcfg⟩ := isRelConfigJC_of_s2_pinch (χ := χ) hp hp0 hc hgc hgi hliftR hpinch hβ' hγ hlift hch
    hS₀S hnR hs hw hw0 hη hwt hηt hcut hcusp hG₀ hGE hG hsE hsu hfl
  exact ⟨LΨ, G₀, GE, G, hLeq, hcfg⟩

/-- **The physical chain from the flow line's generating trace** (in the frame of the upper seed): if `ηu` is a
continuous generating trace of `w` on `[0, ζ]` (`IsFlowLine`'s `η − u`), the witness `β'` agrees with `ηu` up to `a`,
and `t_L + s ≤ a` with `t_L + s < ζ`, then a global chain `(W, η')` from `0` agrees with `β'` on `[0, t_L + s]` and has
hull `fill β'([0, t_L + s])` there. -/
theorem exists_physChain {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ηu β' : ℝ≥0 → ℂ} (hgen : IsGeneratingTrace w ζ ηu)
    (hw : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {a : ℝ≥0} (hβa : ∀ r ≤ a, β' r = ηu r)
    {tL : ℝ≥0} {s : ℝ} (hs : 0 ≤ s) (hta : tL + s.toNNReal ≤ a)
    (htζ : ENNReal.ofReal ((tL : ℝ) + s) < ζ) :
    ∃ (W : ℝ → ℝ) (η' : ℝ → ℂ), Continuous W ∧ W 0 = 0 ∧ IsLoewnerTrace W η' ∧
      fwdHull W ((tL : ℝ) + s) = fillH (β' '' Icc 0 (tL + s.toNNReal)) ∧
      ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), η' r = β' r.toNNReal := by
  have ht0 : (0 : ℝ) ≤ (tL : ℝ) + s := by have := tL.coe_nonneg; linarith
  have hte : ((tL : ℝ) + s).toNNReal = tL + s.toNNReal := by
    rw [Real.toNNReal_add tL.coe_nonneg hs, Real.toNNReal_coe]
  obtain ⟨W, η', hW, hW0, hη', hagree, hK⟩ := exists_globalTrace_of_isGeneratingTrace hgen hw hw0 ht0 htζ
  have hle : ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), r.toNNReal ≤ a := fun r hr => by
    refine le_trans ?_ hta
    rw [← hte]
    exact Real.toNNReal_le_toNNReal hr.2
  refine ⟨W, η', hW, hW0, hη', ?_, fun r hr => by rw [(hagree r hr).2, hβa _ (hle r hr)]⟩
  rw [hK, hte]
  congr 1
  refine Set.EqOn.image_eq fun r hr => (hβa r (hr.2.trans hta)).symm

end InteractingSLE.Theorem14.SB.FinRel
