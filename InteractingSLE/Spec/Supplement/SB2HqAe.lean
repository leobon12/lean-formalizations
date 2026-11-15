/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2HqCfg
import InteractingSLE.Spec.Supplement.SB2JxLate
import InteractingSLE.Spec.Supplement.SB2JxMean

/-!
# SB2(1)'s late (S) line mean, part 12: FIN's configuration almost surely, in FIN's coordinates

Packet PROVE-T14-SB2DRV (round 11). **`ae_relConfigJK_line_of_tip`**: given the named hypothesis
`SB2JxTipStatement`, at every fixed line time `t`, almost surely on the live cell after the entrance, FIN's
configuration `IsRelConfigJK` holds for

* FIN's retained set `A = walkFill − u` (the translated walk fill; `image_translate_eq_fillH` with the chart domain
  identity `ae_dom_eq_H_sdiff_walkFill`),
* FIN's chart `Lw.shiftChart (I.chart ω) u 0` (= the chain record's `Lw.shiftChart (launchChart) u (launchEntry)` by
  `I.chart_eq` and `shiftChart_recenter`), the relative word = the typed cell word, any exploration word,
* exploration time `t`, relative time `a(t)`, the record's drivers and traces (the relative driver = `W` below the
  lifetime, the exploration trace = `η − u` on `[0, t₂)` for some `t₂ > t`).

**R48.** Theorems 1.2–1.3 are not used. The only new-mathematics input is `SB2JxTipStatement` (round 8).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull logDerivFwd)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets Sec6
open Supp8.Q3Chain (flowedData flowedJumps initJumps)

section Line

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ} {I : K2LaunchInputs κ b jumps P h E k u ψ} {u₀ : ℂ → ℝ}
  {D : EntranceUnion κ b jumps P h E k u η ζ u₀}

/-- **FIN's configuration almost surely on the live cell after the entrance, in FIN's coordinates** (from the
per-time chain record and the named hypothesis `SB2JxTipStatement`). -/
theorem ae_relConfigJK_line_of_tip (hT : SB2JxTipStatement.{u}) (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (Vd : SB2LineVersionR HP I D) {wt : WordType} (hwt : wt ∈ I.types) (t : ℝ≥0) {A' : Ω → Set ℂ}
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
  filter_upwards [Vd.chain wt hwt t, hT κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd wt hwt t, I.chart_eq,
    ae_dom_eq_H_sdiff_walkFill HP I hA'ae] with ω hch htip hceq hdom hlive hlate
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hlive.1.1.1
  have hchω := hch hlive.1 hlive.2
  have hce : I.chart ω = (launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω) :=
    hceq hl
  have hconf : (I.chart ω).IsConformal := I.chart_measurable.1 ω
  have htip' := htip hlive hlate
  have hd := hdom hl
  rw [hce] at htip' hconf hd
  have hxL : ∀ i, cellXL κ ψ I.word wt ω i ≤ 0 := (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.1
  have hxR : ∀ j, 0 ≤ cellXR κ ψ I.word wt ω j := (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.2.2
  obtain ⟨Wr, ηr, w, ηw, LΨ, G₀, GE, G, hWr, hηw, hat, hLE, hEq, hcfg⟩ :=
    exists_relConfigJK_of_chainAt (κ := κ) (χ := χ) (ρL := typedRhoL wt) (ρR := typedRhoR wt) (ρL' := ρL')
      (ρR' := ρR') hchω hlate (mem_image_of_mem_dom_recenter hconf htip') hxL hxR hxL' hxR'
  have hAe : (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω =
      fillH ((fun z : ℂ => z - u) '' lowerPrefix κ b jumps E (k + 1) u ω) :=
    image_translate_eq_fillH hconf (walkFill_subset_H A' ω) hd hLE.1.2.1
  have hcs : Lw.shiftChart (I.chart ω) u 0 =
      Lw.shiftChart (launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω) := by
    rw [hce, shiftChart_recenter]
  rw [hAe, hcs]
  exact ⟨Wr, ηr, w, ηw, LΨ, G₀, GE, G, hWr, hηw, hat, hEq, hcfg⟩

end Line

end InteractingSLE.Theorem14.SB.Lv
