/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzOffM

/-!
# The `P`-level canonical stage objects consumed by the transfer to the upper kernel

Packet PROVE-SB2-LCMEAN, round 15 (item 4). The transfer to the upper kernel, the identification with `EL` and the
gluing over the offset (`Mz.ae_codeMatch_of_glued`, `Mz.ident_at_sample`, `Mz.pastSigma_le_aeSigma_of_rec`,
`Mz.exists_measurableSet_relOffEvent`) consume, at every B-stage `ℓ`, canonical objects that do not depend on the
upper-past sample. This file states them:

* **`CanonIdentOn ℓ G c K x₀ Dr`**: on `G`, the canonical hull is the retained fill; the canonical driver
  `driverOf (c, Z)` (`Z` the field read in the hull chart) has positive lifetime and the chain clause (`Mx.ChainFor`)
  of B's piece `ℓ`, in B's stage coordinates; and its record is the record of the driver `Dr`, which is measurable for
  the marks after B's stage `ℓ`;
* **`TailCanonAt ℓ`** (the tail stages, after the start): the objects are measurable for the marks at the start of
  stage `ℓ` (`Ms.stageMarks`), with the conditional GFF law of `Z` given them, and they cover the tail stage events;
* **`RootIdentAt ℓ`** (the start on a piece, `ℓ = relOff`): the identification and record objects of the relative
  root. They cover the samples where B launches at `relOff` a piece of positive lifetime containing `R` in its tips.
  Its law is decided separately (the root decision of round 14; the zero-lifetime and mark roots need nothing);
* **`SB2LowerStageCanonStatement`**: the tail objects at every stage. This is the output form of the joint induction
  (items 1–3 of the split, F2b′, and the kernel half `Mu.*`). `RootIdentAt` is the form for the root's producers.

R48: no source theorem is assumed; this is a named statement for Theorem 1.4's SB2(2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mz

open Restart Exist Exist.Staged Exist.StagedLaw Lu Mx

section Defs

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (b : ℝ → ℝ) (jumps : Finset ℝ)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0))
  (k : ℕ)

/-- B's drivers (the lower walk). -/
abbrev lowerD (ω : Ω) : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω

/-- The retained union at the start of B's stage `ℓ`: the upper prefix and B's physical prefix. -/
abbrev retY (ℓ : ℕ) (ω : Ω) : Set ℂ :=
  upperPrefix κ b jumps E u l k ω ∪
    SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) ℓ

/-- **The identification and record clause of canonical objects on an event.** -/
def CanonIdentOn (ℓ : ℕ) (G : Set Ω) (c : Ω → BoundaryWord) (K : Ω → Set ℂ) (x₀ : Ω → ℝ)
    (Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) : Prop :=
  Measurable[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] Dr ∧ (∀ ω, IsRegularDriver (Dr ω)) ∧
    ∀ᵐ ω ∂P, ω ∈ G → fillH (K ω) = fillH (retY (κ := κ) b jumps E u l k ℓ ω) ∧
      ChainFor (Mn.stageRetained (Mn.walkStageChart κ b jumps E ℓ ω) (retY (κ := κ) b jumps E u l k ℓ ω))
        (stageChartOf (Mn.walkStageChart κ b jumps E ℓ ω) (Mo.hullChart (fillH (K ω)) (x₀ ω)))
        (LuM.trOf (lowerD b jumps E ω ℓ)) (lowerD b jumps E ω ℓ).2
        (driverOf h12p hκ (-(Real.pi / 2))
          (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))) ∧
      (driverOf h12p hκ (-(Real.pi / 2))
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 ≠ 0 ∧
      recOf ⊤ (Dr ω) = recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))

/-- **The canonical objects of a tail stage `ℓ`.** -/
def TailCanonAt (ℓ : ℕ) : Prop :=
  ∃ (G : Set Ω) (c : Ω → BoundaryWord) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)),
    Measurable[Ms.stageMarks κ b jumps E u l k ℓ] c ∧
    @IsDyadicHitMeasurable Ω (Ms.stageMarks κ b jumps E u l k ℓ) K ∧
    Measurable[Ms.stageMarks κ b jumps E u l k ℓ] x₀ ∧
    (∀ᵐ ω₁ ∂P, ω₁ ∈ G → IsGFFWithBoundaryData (condExpKernel P (Ms.stageMarks κ b jumps E u l k ℓ) ω₁)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (c ω₁).fn (c ω₁).jumps) ∧
    (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
        (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (lowerD b jumps E ω) + 2 ≤ ℓ →
      (lowerD b jumps E ω ℓ).2 ≠ 0 → ω ∈ G) ∧
    CanonIdentOn h12p hκ b jumps P h E u l k ℓ G c K x₀ Dr hKc hKp

/-- **The identification objects of the relative root on a piece at B's stage `ℓ = relOff`.** -/
def RootIdentAt (ℓ : ℕ) : Prop :=
  ∃ (G : Set Ω) (c : Ω → BoundaryWord) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)),
    (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (lowerD b jumps E ω) = ℓ →
      ¬ Lk.ArcEntry κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (lowerD b jumps E ω) →
      (lowerD b jumps E ω ℓ).2 ≠ 0 → ω ∈ G) ∧
    CanonIdentOn h12p hκ b jumps P h E u l k ℓ G c K x₀ Dr hKc hKp

end Defs

/-- **Named statement (the output form of the joint induction)**: in SB2(2)'s setting (the premises of
`Lf.SB2LowerSetting`, which do not depend on the upper-past sample), at every B-stage `ℓ`, the canonical objects of a
tail stage. -/
def SB2LowerStageCanonStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k → ∀ ℓ : ℕ, TailCanonAt h12p hκ b jumps P h E u l k ℓ

end InteractingSLE.Theorem14.SB.Mz
