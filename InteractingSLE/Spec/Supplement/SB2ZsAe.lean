/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YtAe
import InteractingSLE.Spec.Supplement.SB2ZsData

/-!
# SB2ZsAe: `SB2YtAe` for the lifetime-generic line version `SB2LineVersionG`

Packet PROVE-T14-SB2DRV (round 15, decision D4: SB2(1) at announced stops). The declarations of `SB2YtAe` that
depend on the line version, for `SB2LineVersionG` (guards `a t < Λ w` in place of `a t < thr`), with the suffix `G`.
The proofs are the landed ones with the guard replaced. No source theorem is replaced.
-/
/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/

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
theorem ae_relConfigJK_lineG (Vd : SB2LineVersionG HP I D) {wt : WordType} (hwt : wt ∈ I.types) (t : ℝ≥0)
    {A' : Ω → Set ℂ}
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) (χ : ℝ)
    {nL' nR' : ℕ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}
    (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j) :
    ∀ᵐ ω ∂P, ω ∈ lineLiveG Vd wt t →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (t : ℝ≥0∞) →
      ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) (w : ℝ → ℝ) (ηw : ℝ → ℂ) (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ),
        (∀ q : ℝ≥0, (q : ℝ≥0∞) <
          Vd.Λ wt ω →
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
theorem ae_exists_isFinCfg_noTipG (Vd : SB2LineVersionG HP I D) {wt : WordType} (hwt : wt ∈ I.types) (t : ℝ≥0)
    {A' : Ω → Set ℂ}
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) :
    ∀ᵐ ω ∂P, ω ∈ lineLiveG Vd wt t →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (t : ℝ≥0∞) →
      ∃ d, IsFinCfgG Vd wt t A' ω d := by
  have hF := Theorem15.isOrderedForceWord_flowLine b jumps u
  filter_upwards [ae_relConfigJK_lineG (ρL' := flowLineRhoL κ b jumps u ψ) (ρR' := flowLineRhoR κ b jumps u ψ)
    Vd hwt t hA'ae (chiC κ) hF.2.1 hF.2.2.2] with ω hω hl hlate
  obtain ⟨Wr, ηr, w, ηw, LΨ, G₀, GE, G, h1, h2, h3, h4, h5⟩ := hω hl hlate
  exact ⟨⟨Wr, ηr, w, ηw, LΨ, G₀, GE, G⟩, h1, h2, h3, h4, h5⟩
end Line

end InteractingSLE.Theorem14.SB.Lv

