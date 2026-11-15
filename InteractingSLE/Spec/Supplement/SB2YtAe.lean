/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YtCfg
import InteractingSLE.Spec.Supplement.SB2FzData
import InteractingSLE.Spec.Supplement.OrdGapFixed

/-!
# FIN's configuration at a fixed line time without the tip condition

Packet PROVE-T14-SB2DRV (round 13). The named hypothesis `SB2JxTipStatement` (round 8: the upper flow's tip at a
fixed line time is in the launch chart's domain) is not needed. FIN's configuration only needs the physical tip in
`ℍ` (`FinRel.isRelConfigJK_of_s2_liftOn_noTip`), and at a fixed positive time this is
`RLC.OrdLate.ae_mem_H_at` (no force gap is zero at a fixed time; PROVE-ABSMERGE / PROVE-T15-ORDDET5).

* **`exists_relConfigJK_of_chainAt_noTip`**: `exists_relConfigJK_of_chainAt` (`SB2HqCfg`) with `η t ∈ ℍ` in place of
  the tip condition;
* **`ae_relConfigJK_line`**: `ae_relConfigJK_line_of_tip` (`SB2HqAe`) without `SB2JxTipStatement`;
* **`ae_exists_isFinCfg_noTip`**: `ae_exists_isFinCfg` (`SB2FzData`) without `SB2JxTipStatement`.

**R48.** Theorems 1.2–1.3 are not used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdMap fwdHull logDerivFwd)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Supp8.Q3Chain (flowedData flowedJumps initJumps)

/-- **FIN's configuration at a fixed line time from the per-time chain record, with the physical tip in `ℍ`.** -/
theorem exists_relConfigJK_of_chainAt_noTip {A : Set ℂ} {u m : ℝ} {c : Chart} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞}
    {W : ℝ≥0 → ℝ} {a : ℝ≥0 → ℝ≥0∞} {V : ℝ≥0∞} {t : ℝ≥0} (hch : Tc.IsSB2LineChainAt A u m c η ζ W a V t)
    (hlate : firstVisit η ζ (realMin A) < (t : ℝ≥0∞)) (hηH : η t ∈ H) {κ χ : ℝ}
    {nL nR nL' nR' : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) (w : ℝ → ℝ) (ηw : ℝ → ℂ) (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ),
      (∀ q : ℝ≥0, (q : ℝ≥0∞) < V → W q = Wr q) ∧
      (∃ t₂ : ℝ, (t : ℝ) < t₂ ∧ ∀ r : ℝ, 0 ≤ r → r < t₂ → ηw r = η r.toNNReal - u) ∧
      a t ≠ ⊤ ∧ IsLeftEntryChart ((fun z : ℂ => z - u) '' A) (realMin ((fun z : ℂ => z - u) '' A))
        (Lw.shiftChart c u m) ∧
      EqOn (Lw.shiftChart c u m).2.2 (fun z => (LΨ z).im) (H \ fillH ((fun z : ℂ => z - u) '' A)) ∧
      FinRel.IsRelConfigJK (fillH ((fun z : ℂ => z - u) '' A)) (Lw.shiftChart c u m).1 (Lw.shiftChart c u m).2.1 LΨ ∅ w
        Wr ηw ηr t ((a t).toNNReal : ℝ) χ (Real.pi / Real.sqrt κ) (forceBoundaryData κ ρL ρR xL xR)
        (flowedData κ ρL' ρR' xL' xR' w t) (flowedData κ ρL ρR xL xR Wr ((a t).toNNReal : ℝ))
        (initJumps xL xR) (flowedJumps xL' xR' w t) (flowedJumps xL xR Wr ((a t).toNNReal : ℝ)) G₀ GE G
        (fun z => G (fwdMap Wr ((a t).toNNReal : ℝ) ((Lw.shiftChart c u m).1 z)) -
          χ * ((logDerivFwd Wr ((a t).toNNReal : ℝ) ((Lw.shiftChart c u m).1 z)).im + (LΨ z).im)) := by
  obtain ⟨p, g, β', γ, tL, S, Wr, ηr, w, ηw, htS, ⟨hp, hp0, hpH, -, hpA⟩, ⟨hc, hgc, hgi, hgf, hL⟩,
    ⟨hβ', hβ'0, hA, htL, htLv, hγ, hγ0, hlift⟩, hβη, ⟨-, hchS, hnR⟩, ⟨hw, hw0, hηw, hwt, hηβ⟩,
    ⟨hWr, -, ha⟩⟩ := hch
  have htLt : tL < t := by
    have : ((tL : ℝ≥0) : ℝ≥0∞) < t := htLv ▸ hlate
    exact_mod_cast this
  have htLt' : (tL : ℝ) < t := htLt
  set s : ℝ := (t : ℝ) - tL with hs_def
  have hs0 : 0 < s := by rw [hs_def]; linarith
  have hsS : s < S := by rw [hs_def]; linarith
  have hts : (tL : ℝ) + s = t := by rw [hs_def]; ring
  have hηβ' : ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), ηw r = β' r.toNNReal := fun r hr =>
    hηβ r hr.1 (by rw [hts] at hr; linarith [hr.2])
  have hηH' : ηw ((tL : ℝ) + s) ∈ H := by
    rw [hts, hηβ t t.coe_nonneg htS, Real.toNNReal_coe, hβη t htS]
    show 0 < (η t - (u : ℂ)).im
    have : 0 < (η t).im := hηH
    simpa using this
  obtain ⟨LΨ, G₀, GE, G, hEq, hcfg⟩ := FinRel.isRelConfigJK_of_s2_liftOn_noTip (κ := κ) (χ := χ) (ρL := ρL) (ρR := ρR)
    (ρL' := ρL') (ρR' := ρR') hxL hxR hxL' hxR' hp hp0 hpH hc hgc hgi hgf hL hβ' hβ'0 hA htL hγ hγ0 hlift
    (hchS s hs0.le hsS) hsS hnR ⟨hs0, le_rfl⟩ hw hw0 hηw (hwt s hs0 hsS) hηβ' hηH'
  have hat : a t = ((Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s).toNNReal : ℝ≥0∞) :=
    ha t htLt.le htS
  have hcap : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s = ((a t).toNNReal : ℝ) := by
    rw [hat, ENNReal.toNNReal_coe, Real.coe_toNNReal _ hcfg.hu]
  rw [hts, hcap, hpA] at hcfg
  rw [hpA] at hEq hc
  refine ⟨Wr, ηr, w, ηw, LΨ, G₀, GE, G, hWr, ⟨(tL : ℝ) + S, htS, fun r hr0 hrt' => ?_⟩,
    by rw [hat]; exact ENNReal.coe_ne_top, hc, hEq, hcfg⟩
  rw [hηβ r hr0 hrt', hβη _ (by rw [Real.coe_toNNReal _ hr0]; exact hrt')]

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets Sec6

section Line

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ} {I : K2LaunchInputs κ b jumps P h E k u ψ} {u₀ : ℂ → ℝ}
  {D : EntranceUnion κ b jumps P h E k u η ζ u₀}

/-- **FIN's configuration almost surely on the live cell after the entrance, in FIN's coordinates** (from the
per-time chain record and the fixed-time interior of the flow, `OrdLate.ae_mem_H_at`; no named input). -/
theorem ae_relConfigJK_line (Vd : SB2LineVersionR HP I D) {wt : WordType} (hwt : wt ∈ I.types) (t : ℝ≥0)
    {A' : Ω → Set ℂ}
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) (χ : ℝ)
    {nL' nR' : ℕ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}
    (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j) :
    ∀ᵐ ω ∂P, ω ∈ lineLive Vd wt t →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (t : ℝ≥0∞) →
      ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) (w : ℝ → ℝ) (ηw : ℝ → ℂ) (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ),
        (∀ q : ℝ≥0, (q : ℝ≥0∞) <
          FCDet.thr (typedRhoL wt) (typedRhoR wt) Vd.W (cellXL κ ψ I.word wt) (cellXR κ ψ I.word wt) ω →
          Vd.W q ω = Wr q) ∧
        (∃ t₂ : ℝ, (t : ℝ) < t₂ ∧ ∀ r : ℝ, 0 ≤ r → r < t₂ → ηw r = η ω r.toNNReal - u) ∧ Vd.a t ω ≠ ⊤ ∧
        EqOn (Lw.shiftChart (I.chart ω) u 0).2.2 (fun z => (LΨ z).im)
          (H \ (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω) ∧
        FinRel.IsRelConfigJK ((fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω)
          (Lw.shiftChart (I.chart ω) u 0).1 (Lw.shiftChart (I.chart ω) u 0).2.1 LΨ ∅ w Wr ηw ηr t
          ((Vd.a t ω).toNNReal : ℝ) χ (Real.pi / Real.sqrt κ)
          (forceBoundaryData κ (typedRhoL wt) (typedRhoR wt) (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω))
          (flowedData κ ρL' ρR' xL' xR' w t)
          (flowedData κ (typedRhoL wt) (typedRhoR wt) (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω) Wr
            ((Vd.a t ω).toNNReal : ℝ))
          (initJumps (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω)) (flowedJumps xL' xR' w t)
          (flowedJumps (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω) Wr ((Vd.a t ω).toNNReal : ℝ)) G₀ GE G
          (fun z => G (fwdMap Wr ((Vd.a t ω).toNNReal : ℝ) ((Lw.shiftChart (I.chart ω) u 0).1 z)) -
            χ * ((logDerivFwd Wr ((Vd.a t ω).toNNReal : ℝ) ((Lw.shiftChart (I.chart ω) u 0).1 z)).im +
              (LΨ z).im)) := by
  rcases eq_zero_or_pos t with ht0 | htpos
  · refine ae_of_all _ fun ω _ hlate => absurd hlate ?_
    rw [ht0, ENNReal.coe_zero]
    exact not_lt_zero
  filter_upwards [Vd.chain wt hwt t, RLC.OrdLate.ae_mem_H_at HP.kappa_pos HP.kappa_lt_four.le HP.flow t htpos,
    I.chart_eq, ae_dom_eq_H_sdiff_walkFill HP I hA'ae, Vd.alive wt hwt t] with ω hch hηHω hceq hdom halω hlive hlate
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hlive.1.1.1
  have hchω := hch hlive.1 hlive.2
  have hce : I.chart ω = (launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω) :=
    hceq hl
  have hconf : (I.chart ω).IsConformal := I.chart_measurable.1 ω
  have hηH := hηHω (halω hlive.1 hlive.2)
  have hd := hdom hl
  rw [hce] at hconf hd
  have hxL : ∀ i, cellXL κ ψ I.word wt ω i ≤ 0 := (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.1
  have hxR : ∀ j, 0 ≤ cellXR κ ψ I.word wt ω j := (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.2.2
  obtain ⟨Wr, ηr, w, ηw, LΨ, G₀, GE, G, hWr, hηw, hat, hLE, hEq, hcfg⟩ :=
    exists_relConfigJK_of_chainAt_noTip (κ := κ) (χ := χ) (ρL := typedRhoL wt) (ρR := typedRhoR wt) (ρL' := ρL')
      (ρR' := ρR') hchω hlate hηH hxL hxR hxL' hxR'
  have hAe : (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω =
      fillH ((fun z : ℂ => z - u) '' lowerPrefix κ b jumps E (k + 1) u ω) :=
    image_translate_eq_fillH hconf (walkFill_subset_H A' ω) hd hLE.1.2.1
  have hcs : Lw.shiftChart (I.chart ω) u 0 =
      Lw.shiftChart (launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω) := by
    rw [hce, shiftChart_recenter]
  rw [hAe, hcs]
  exact ⟨Wr, ηr, w, ηw, LΨ, G₀, GE, G, hWr, hηw, hat, hEq, hcfg⟩

/-- **Some configuration data exist almost surely on the live cell after the entrance** (no named input). -/
theorem ae_exists_isFinCfg_noTip (Vd : SB2LineVersionR HP I D) {wt : WordType} (hwt : wt ∈ I.types) (t : ℝ≥0)
    {A' : Ω → Set ℂ}
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) :
    ∀ᵐ ω ∂P, ω ∈ lineLive Vd wt t →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (t : ℝ≥0∞) →
      ∃ d, IsFinCfg Vd wt t A' ω d := by
  have hF := Theorem15.isOrderedForceWord_flowLine b jumps u
  filter_upwards [ae_relConfigJK_line (ρL' := flowLineRhoL κ b jumps u ψ) (ρR' := flowLineRhoR κ b jumps u ψ)
    Vd hwt t hA'ae (chiC κ) hF.2.1 hF.2.2.2] with ω hω hl hlate
  obtain ⟨Wr, ηr, w, ηw, LΨ, G₀, GE, G, h1, h2, h3, h4, h5⟩ := hω hl hlate
  exact ⟨⟨Wr, ηr, w, ηw, LΨ, G₀, GE, G⟩, h1, h2, h3, h4, h5⟩

end Line

end InteractingSLE.Theorem14.SB.Lv
