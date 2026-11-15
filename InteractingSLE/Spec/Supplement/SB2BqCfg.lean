/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2BqPath
import InteractingSLE.Spec.Supplement.SB2YtCfg
import InteractingSLE.Spec.Supplement.SB2LmMirror
import InteractingSLE.Spec.Supplement.SB2NqChain

/-!
# SB2(2)'s configuration at a later relative stage by the bridge (ruling R120; D5 F1, D11 (G2))

Packet PROVE-GW2-GEOM2. SB2(1)'s configuration constructors `FinRel.isRelConfigJK_of_s2_liftOn` and
`FinRel.isRelConfigJK_of_s2_liftOn_noTip` applied to R120's retained path `Bq.bridgePath x₁ q` (the real segment
`[0, x₁]` followed by the lifted upper prefix `q`) with head time `tL = 0`, and the result read on any retained set
`R` with `fill R = fill q([0, 1])` (only the filling enters).

* **`isRelConfigJK_of_bridgePath`** (the lift's tip in `ℍ`) and **`isRelConfigJK_of_bridgePath_noTip`** (only the
  explored tip in `ℍ`): the configuration `IsRelConfigJK (fill R) …` at explored time `s` (PROVE-SB2-LCMEAN's F1);
* **`isRelConfigJKL_of_bridgePath_noTip`**: the same, reflected, as `Lm.IsRelConfigJKL` (the mirrored picture of
  SB2(2), retained set on the left);
* **`exists_relConfig_bridgePath_noTip`**: the full builder — the S2 lift `γ` of the explored piece from time `0`, its
  relative chain `(Wr, ηr)`, and the configuration at every `s ∈ (0, S₀]`;
* **`exists_isSB2RelChain_of_lim_zero`**: PROVE-T14-SB2LIFT's (G2) in the form of `Mn.StageChainAtR` (head time `0`,
  boundary limits along the lift before the lifetime, the retained set `X ⊆ ℍ` relatively closed with a domain chart
  of `ℍ ∖ X` taking `∞` to `∞`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv logDerivFwd)
open InteractingSLE.Supp9B (IsProperCurve closedRightSide)

namespace InteractingSLE.Theorem14.SB.Bq

open Sec7.Lemma71C FinRel
open WangWu (chartAL chartAR)
open Supp8.BHMean (jointInv IsSideWord IsFlowedWord)
open Supp8.Q3Chain (flowedData flowedJumps initJumps)
open LP (reflectC)
open Sec7.FlowReflect (reflData reflJumps)

section Config

variable {q : ℝ → ℂ} {x₁ : ℝ} {R : Set ℂ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ}
  {S₀ Sm : ℝ} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {w : ℝ → ℝ} {η : ℝ → ℂ} {κ χ : ℝ}
  {nL nR nL' nR' : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}

/-- The left entry chart at `realMin = 0` of the bridge, from that of `R`. -/
theorem isLeftEntryChart_bridgePath (hq0 : q 0 = x₁) (hx₁ : 0 ≤ x₁)
    (hqR : ∀ y : ℝ, (y : ℂ) ∈ q '' Icc 0 1 → 0 ≤ y) (hR : fillH R = fillH (q '' Icc 0 1))
    (hc : IsLeftEntryChart R 0 c) :
    IsLeftEntryChart (bridgePath x₁ q '' Icc 0 1) (realMin (bridgePath x₁ q '' Icc 0 1)) c := by
  rw [realMin_image_bridgePath hx₁ hq0 hqR]
  exact (isLeftEntryChart_congr_fillH ((fillH_image_bridgePath hx₁ hq0).trans hR.symm)).2 hc

/-- **SB2(2)'s configuration at a later relative stage by the bridge, only the explored tip in `ℍ`**
(`FinRel.isRelConfigJK_of_s2_liftOn_noTip` for `bridgePath x₁ q` with head time `0`). -/
theorem isRelConfigJK_of_bridgePath_noTip
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
    (hq : ContinuousOn q (Icc 0 1)) (hq0 : q 0 = x₁) (hx₁ : 0 ≤ x₁)
    (hqH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (q s).im) (hqR : ∀ y : ℝ, (y : ℂ) ∈ q '' Icc 0 1 → 0 ≤ y)
    (hR : fillH R = fillH (q '' Icc 0 1)) (hc : IsLeftEntryChart R 0 c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) (hL : LiftRealOn c)
    (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : q '' Icc 0 1 ⊆ closedRightSide β')
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hlift : ∀ s, g (γ s) = β' s)
    (hch : IsSB2RelChain R c β' γ 0 S₀ Wr ηr) (hS₀S : S₀ < Sm)
    (hnR : interior {r ∈ Ioo (0 : ℝ) Sm | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅)
    {s : ℝ} (hs : s ∈ Ioc 0 S₀) (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η)
    (hwt : fwdHull w s = fillH (β' '' Icc 0 s.toNNReal))
    (hηβ : ∀ r ∈ Icc (0 : ℝ) s, η r = β' r.toNNReal) (hηH : η s ∈ H) :
    ∃ (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ), EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH R) ∧
      IsRelConfigJK (fillH R) c.1 c.2.1 LΨ ∅ w Wr η ηr s
        (capClock (fun r : ℝ => γ r.toNNReal) s) χ (Real.pi / Real.sqrt κ) (forceBoundaryData κ ρL ρR xL xR)
        (flowedData κ ρL' ρR' xL' xR' w s)
        (flowedData κ ρL ρR xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (initJumps xL xR)
        (flowedJumps xL' xR' w s) (flowedJumps xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
        G₀ GE G
        (fun z => G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)) -
          χ * ((logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)).im + (LΨ z).im)) := by
  have hfill : fillH (bridgePath x₁ q '' Icc 0 1) = fillH R := (fillH_image_bridgePath hx₁ hq0).trans hR.symm
  have hmin := realMin_image_bridgePath hx₁ hq0 hqR
  have h := isRelConfigJK_of_s2_liftOn_noTip (tL := 0) (κ := κ) (χ := χ) (ρL := ρL) (ρR := ρR) (ρL' := ρL')
    (ρR' := ρR') hxL hxR hxL' hxR' (continuousOn_bridgePath hq) (bridgePath_zero hq0)
    (im_bridgePath_nonneg hq0 hqH) (isLeftEntryChart_bridgePath hq0 hx₁ hqR hR hc) hgc hgi hgf hL hβ' hβ'0
    (image_bridgePath_subset_closedRightSide hx₁ hq0 hβ' hβ'0 hA) (by rw [hmin, hβ'0, ofReal_zero]) hγ hγ0
    (fun s => by rw [zero_add]; exact hlift s) ((isSB2RelChain_congr_fillH hfill).2 hch) hS₀S
    (by simpa only [zero_add] using hnR) hs hw hw0 hη (by simpa only [NNReal.coe_zero, zero_add] using hwt)
    (by simpa only [NNReal.coe_zero, zero_add] using hηβ) (by simpa only [NNReal.coe_zero, zero_add] using hηH)
  simp only [NNReal.coe_zero, zero_add] at h
  rw [hfill] at h
  exact h

/-- **SB2(2)'s configuration at a later relative stage by the bridge, the lift's tip in `ℍ`**
(`FinRel.isRelConfigJK_of_s2_liftOn` for `bridgePath x₁ q` with head time `0`). -/
theorem isRelConfigJK_of_bridgePath
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
    (hq : ContinuousOn q (Icc 0 1)) (hq0 : q 0 = x₁) (hx₁ : 0 ≤ x₁)
    (hqH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (q s).im) (hqR : ∀ y : ℝ, (y : ℂ) ∈ q '' Icc 0 1 → 0 ≤ y)
    (hR : fillH R = fillH (q '' Icc 0 1)) (hc : IsLeftEntryChart R 0 c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) (hL : LiftRealOn c)
    (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : q '' Icc 0 1 ⊆ closedRightSide β')
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hlift : ∀ s, g (γ s) = β' s)
    (hch : IsSB2RelChain R c β' γ 0 S₀ Wr ηr) (hS₀S : S₀ < Sm)
    (hnR : interior {r ∈ Ioo (0 : ℝ) Sm | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅)
    {s : ℝ} (hs : s ∈ Ioc 0 S₀) (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η)
    (hwt : fwdHull w s = fillH (β' '' Icc 0 s.toNNReal))
    (hηβ : ∀ r ∈ Icc (0 : ℝ) s, η r = β' r.toNNReal) (hγH : γ s.toNNReal ∈ H) :
    ∃ (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ), EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH R) ∧
      IsRelConfigJK (fillH R) c.1 c.2.1 LΨ ∅ w Wr η ηr s
        (capClock (fun r : ℝ => γ r.toNNReal) s) χ (Real.pi / Real.sqrt κ) (forceBoundaryData κ ρL ρR xL xR)
        (flowedData κ ρL' ρR' xL' xR' w s)
        (flowedData κ ρL ρR xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (initJumps xL xR)
        (flowedJumps xL' xR' w s) (flowedJumps xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
        G₀ GE G
        (fun z => G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)) -
          χ * ((logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)).im + (LΨ z).im)) := by
  have hfill : fillH (bridgePath x₁ q '' Icc 0 1) = fillH R := (fillH_image_bridgePath hx₁ hq0).trans hR.symm
  have hmin := realMin_image_bridgePath hx₁ hq0 hqR
  have h := isRelConfigJK_of_s2_liftOn (tL := 0) (κ := κ) (χ := χ) (ρL := ρL) (ρR := ρR) (ρL' := ρL')
    (ρR' := ρR') hxL hxR hxL' hxR' (continuousOn_bridgePath hq) (bridgePath_zero hq0)
    (im_bridgePath_nonneg hq0 hqH) (isLeftEntryChart_bridgePath hq0 hx₁ hqR hR hc) hgc hgi hgf hL hβ' hβ'0
    (image_bridgePath_subset_closedRightSide hx₁ hq0 hβ' hβ'0 hA) (by rw [hmin, hβ'0, ofReal_zero]) hγ hγ0
    (fun s => by rw [zero_add]; exact hlift s) ((isSB2RelChain_congr_fillH hfill).2 hch) hS₀S
    (by simpa only [zero_add] using hnR) hs hw hw0 hη (by simpa only [NNReal.coe_zero, zero_add] using hwt)
    (by simpa only [NNReal.coe_zero, zero_add] using hηβ) hγH
  simp only [NNReal.coe_zero, zero_add] at h
  rw [hfill] at h
  exact h

/-- **The mirrored configuration at a later relative stage by the bridge** (SB2(2)'s picture, retained set on the
left): `Lm.isRelConfigJKL_of_reflect` applied to `isRelConfigJK_of_bridgePath_noTip` for the reflected data. -/
theorem isRelConfigJKL_of_bridgePath_noTip
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
    (hq : ContinuousOn q (Icc 0 1)) (hq0 : q 0 = x₁) (hx₁ : 0 ≤ x₁)
    (hqH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (q s).im) (hqR : ∀ y : ℝ, (y : ℂ) ∈ q '' Icc 0 1 → 0 ≤ y)
    (hR : fillH R = fillH (q '' Icc 0 1)) (hc : IsLeftEntryChart R 0 c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) (hL : LiftRealOn c)
    (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : q '' Icc 0 1 ⊆ closedRightSide β')
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hlift : ∀ s, g (γ s) = β' s)
    (hch : IsSB2RelChain R c β' γ 0 S₀ Wr ηr) (hS₀S : S₀ < Sm)
    (hnR : interior {r ∈ Ioo (0 : ℝ) Sm | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅)
    {s : ℝ} (hs : s ∈ Ioc 0 S₀) (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η)
    (hwt : fwdHull w s = fillH (β' '' Icc 0 s.toNNReal))
    (hηβ : ∀ r ∈ Icc (0 : ℝ) s, η r = β' r.toNNReal) (hηH : η s ∈ H) :
    ∃ (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ), EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH R) ∧
      Lm.IsRelConfigJKL (reflectC '' fillH R) (fun z => reflectC (c.1 (reflectC z)))
        (fun z => reflectC (c.2.1 (reflectC z))) (fun z => conj (LΨ (reflectC z))) (reflJumps ∅) (-w) (-Wr)
        (fun t => reflectC (η t)) (fun t => reflectC (ηr t)) s
        (capClock (fun r : ℝ => γ r.toNNReal) s) χ (Real.pi / Real.sqrt κ)
        (reflData (forceBoundaryData κ ρL ρR xL xR)) (reflData (flowedData κ ρL' ρR' xL' xR' w s))
        (reflData (flowedData κ ρL ρR xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)))
        (reflJumps (initJumps xL xR)) (reflJumps (flowedJumps xL' xR' w s))
        (reflJumps (flowedJumps xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)))
        (fun z => -G₀ (reflectC z)) (fun z => -GE (reflectC z)) (fun z => -G (reflectC z))
        (fun z => -(G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 (reflectC z))) -
          χ * ((logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 (reflectC z))).im +
            (LΨ (reflectC z)).im))) := by
  obtain ⟨LΨ, G₀, GE, G, hLeq, hcfg⟩ := isRelConfigJK_of_bridgePath_noTip (κ := κ) (χ := χ) (ρL := ρL)
    (ρR := ρR) (ρL' := ρL') (ρR' := ρR') hxL hxR hxL' hxR' hq hq0 hx₁ hqH hqR hR hc hgc hgi hgf hL hβ' hβ'0 hA
    hγ hγ0 hlift hch hS₀S hnR hs hw hw0 hη hwt hηβ hηH
  exact ⟨LΨ, G₀, GE, G, hLeq, Lm.isRelConfigJKL_of_reflect hcfg⟩

/-- **The builder at a later relative stage by the bridge** (D5 F1): the S2 lift `γ` of the explored piece from time
`0`, its relative chain `(Wr, ηr)`, and SB2(1)'s configuration at every explored time `s ∈ (0, S₀]` at which the
explored trace `η` of a continuous driver `w` from `0` follows `β'`, fills like `β'`, and has its tip in `ℍ`. -/
theorem exists_relConfig_bridgePath_noTip (κ χ : ℝ)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
    (hq : ContinuousOn q (Icc 0 1)) (hq0 : q 0 = x₁) (hx₁ : 0 ≤ x₁)
    (hqH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (q s).im) (hqR : ∀ y : ℝ, (y : ℂ) ∈ q '' Icc 0 1 → 0 ≤ y)
    (hR : fillH R = fillH (q '' Icc 0 1)) (hc : IsLeftEntryChart R 0 c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) (hL : LiftRealOn c)
    (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : q '' Icc 0 1 ⊆ closedRightSide β')
    (hS₀ : 0 ≤ S₀) (hS₀S : S₀ < Sm)
    (hnA : interior {r ∈ Ioo (0 : ℝ) Sm | β' r.toNNReal ∈ q '' Icc 0 1} = ∅)
    (hnR : interior {r ∈ Ioo (0 : ℝ) Sm | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅) :
    ∃ γ : ℝ≥0 → ℂ, IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β' s) ∧
      ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), IsSB2RelChain R c β' γ 0 S₀ Wr ηr ∧
        ∀ (w : ℝ → ℝ) (η : ℝ → ℂ) (s : ℝ), s ∈ Ioc 0 S₀ → Continuous w → w 0 = 0 → IsLoewnerTrace w η →
          fwdHull w s = fillH (β' '' Icc 0 s.toNNReal) → (∀ r ∈ Icc (0 : ℝ) s, η r = β' r.toNNReal) →
          η s ∈ H →
          ∃ (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ), EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH R) ∧
            IsRelConfigJK (fillH R) c.1 c.2.1 LΨ ∅ w Wr η ηr s
              (capClock (fun r : ℝ => γ r.toNNReal) s) χ (Real.pi / Real.sqrt κ)
              (forceBoundaryData κ ρL ρR xL xR) (flowedData κ ρL' ρR' xL' xR' w s)
              (flowedData κ ρL ρR xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (initJumps xL xR)
              (flowedJumps xL' xR' w s) (flowedJumps xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
              G₀ GE G
              (fun z => G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)) -
                χ * ((logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)).im + (LΨ z).im)) := by
  obtain ⟨γ, hγ, hγ0, hlift, Wr, ηr, hch⟩ := exists_lift_isSB2RelChain_bridgePath hq hq0 hx₁ hqH hqR hR hc hgc
    hgi hgf hβ' hβ'0 hA hS₀ hS₀S hnA hnR
  refine ⟨γ, hγ, hγ0, hlift, Wr, ηr, hch, fun w η s hs hw hw0 hη hwt hηβ hηH => ?_⟩
  exact isRelConfigJK_of_bridgePath_noTip (κ := κ) (χ := χ) hxL hxR hxL' hxR' hq hq0 hx₁ hqH hqR hR hc hgc hgi
    hgf hL hβ' hβ'0 hA hγ hγ0 hlift hch hS₀S hnR hs hw hw0 hη hwt hηβ hηH

end Config

/-! ### SB2LIFT's (G2): the chain from boundary limits along the lift, head time `0` -/

section Lim

variable {X : Set ℂ} {c : Chart} {β' γ : ℝ≥0 → ℂ}

/-- **SB2(2)'s (G2) in the form of `Mn.StageChainAtR`** (head time `0`): for a retained set `X ⊆ ℍ` (bounded,
relatively closed, `X ∪ {im ≤ 0}` preconnected) with a domain chart of `ℍ ∖ X` taking `∞` to `∞`, an explored piece
`β'` from `0` continuous on `[0, S]`, and a proper lift `γ` from `0` along which the chart inverse has the boundary
limits `β'` on `[0, S]`, with no open time interval of `β'` on `closure X` or on `ℝ` in `(0, S)`: the relative chain
of `γ` exists for every `S₀ < S`. Only boundary limits before `S` enter (no global extension of the chart inverse,
no behaviour of `β'` after `S`). -/
theorem exists_isSB2RelChain_of_lim_zero (hXH : X ⊆ H) (hXb : IsBounded X) (hXc : closure X ∩ H ⊆ X)
    (hXp : IsPreconnected (X ∪ {z : ℂ | z.im ≤ 0})) (hD : IsDomainChart (H \ X) c)
    (hinf : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ X)) (cobounded ℂ)) {S S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀S : S₀ < S)
    (hβc : ContinuousOn β' (Icc 0 S.toNNReal)) (hβ'0 : β' 0 = 0) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlim : ∀ s : ℝ≥0, (s : ℝ) ≤ S → Tendsto c.2.1 (𝓝[H] (γ s)) (𝓝 (β' s)))
    (hnA : interior {r ∈ Ioo (0 : ℝ) S | β' r.toNNReal ∈ closure X} = ∅)
    (hnR : interior {r ∈ Ioo (0 : ℝ) S | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), IsSB2RelChain X c β' γ 0 S₀ Wr ηr := by
  have hfX : fillH X = X := Nq.fillH_eq_self_of_isDomainChart hXH hXb hXc hD
  have hD' : IsDomainChart (H \ fillH X) c := by rw [hfX]; exact hD
  have hinf' : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ fillH X)) (cobounded ℂ) := by rw [hfX]; exact hinf
  obtain ⟨C₁, C₂, hC₁, hgrow⟩ := Nq.exists_growth_inv_of_cobounded hXb hXp hD' hinf'
  have hpre : ∀ r ≤ (0 : ℝ≥0), β' r ∉ H \ fillH X := by
    intro r hr hmem
    have hr0 : r = 0 := le_antisymm hr bot_le
    rw [hr0, hβ'0] at hmem
    have h0 : 0 < (0 : ℂ).im := hmem.1
    simp at h0
  exact Nq.exists_isSB2RelChain_of_lim hD' hC₁ hgrow hS₀ hS₀S (by simpa only [zero_add] using hβc) hpre hγ hγ0
    (fun s hs => by rw [zero_add]; exact hlim s hs) (by simpa only [zero_add] using hnA)
    (by simpa only [zero_add] using hnR)

end Lim

end InteractingSLE.Theorem14.SB.Bq
