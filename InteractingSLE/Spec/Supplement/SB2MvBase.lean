/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuShift

/-!
# The base of the retained-law induction: the form LCMEAN consumes (for PROVE-GW2-GEOM2)

Packet PROVE-SB2-LCMEAN, round 14 (orchestrator work split after ruling R121: the BASE of the induction — the retained
law at the relative root `j = 0` and at the erased stages — goes to PROVE-GW2-GEOM2). This file states, with its exact
Lean type, the form the kernel half consumes.

**`SB2LowerBaseLawStatement`.** In SB2(2)'s setting, at every stage `ℓ` of the lower walk B, for the line family of
`Ml.exists_sb2LineFamily_cf` (filtration `𝓖` with its defining equation, sets `A₁ t`, `A₂ t`): there are
* a retained hull `K` — compact, `K ∪ {im ≤ 0}` preconnected at every sample, dyadic-hit measurable for the completed
  initial line σ-algebra `Ms.lineFiltC P 𝓖 0` (upper past through `k` ⊔ lower past through stage `ℓ` at B-time `0`);
* a `lineFiltC P 𝓖 0`-event `G` containing, almost surely, the stage event at every stage `ℓ` with `ℓ ≤ relOff`
  (the relative root `ℓ = relOff` and the erased stages `ℓ < relOff`), on which `fill K = A₁ 0`;
* the field `Y` read in the canonical hull chart `Mo.hullChart (fillH (K ω)) 0` (offset `0`, as in the reviewer's
  `Qr.RetainedLawAt`) on `G`, measurable;
* a sorted word `β`, `lineFiltC P 𝓖 0`-measurable, with data bounded by one constant `M`;

such that on `G`, conditionally on `lineFiltC P 𝓖 0`, `Y` is a GFF with the data of `β`.

This is `Qr.RetainedLawAt` with the marks of the kernel half (the version's initial σ-algebra,
`Ms.SB2LowerStageVersionStatement` / `Mu.SB2LowerStageVersionStatement2`) and the uniform bound K2's integrability
needs (`Mu.integrableOn_chartPairing_of_law`).
At these stages `fill(A ∪ B_{<ℓ}) = fill A` (LIFTSET's `head_of_arcStart`, `head_of_pieceStart`): the law is the upper
walk's stage witness at `k` read in the canonical hull chart (`S3.exists_stageWitness_interiorStageSides`,
`Qr.exists_hullWord_mean`), with B's erased records as extra marks on the same set (the nested conditional-variance
identity, `Lcd.ae_map_condExpKernel_eq_of_norm_eq`, `Lcd.ae_isGFF_condExpKernel_of_le`). The consumer moves it to the
version's chart offset with `Mu.ae_isGFF_hullChart_shift`.

R48: no source theorem is assumed; this is a named statement for Theorem 1.4's SB2(2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mv

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Supp9B Lx Lk Mf Ms

/-- **Named statement (the base of the retained-law induction; PROVE-GW2-GEOM2's, orchestrator split after R121)**:
the retained kernel law at the relative root and at the erased stages, in the form the kernel half consumes. -/
def SB2LowerBaseLawStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
    ∀ (ℓ : ℕ) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ) (A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
          ω ∧
        A₂ t ω = fillVer (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
            (ℓ + 1)) ω) →
    ∃ (K : Ω → Set ℂ) (G : Set Ω) (Y : Ω → DistOn upperHalfPlaneOpens) (β : Ω → BoundaryWord) (M : ℝ),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K ∧ (∀ ω, IsCompact (K ω)) ∧
      (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧
      MeasurableSet[lineFiltC P 𝓖 0] G ∧
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) → ω ∈ G) ∧
      (∀ᵐ ω ∂P, ω ∈ G → fillH (K ω) = A₁ 0 ω) ∧ Measurable Y ∧
      (∀ᵐ ω ∂P, ω ∈ G → IsChartTransport (Mo.hullChart (fillH (K ω)) 0) 1 0 (chiC κ) (h ω) (Y ω)) ∧
      Measurable[lineFiltC P 𝓖 0] β ∧ (∀ ω, (β ω).IsSorted) ∧ 0 ≤ M ∧
      (∀ ω, ∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M) ∧
      ∀ᵐ ω ∂P, ω ∈ G →
        IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω) Y (β ω).fn (β ω).jumps

end InteractingSLE.Theorem14.SB.Mv
