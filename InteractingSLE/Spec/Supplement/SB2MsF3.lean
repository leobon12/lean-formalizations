/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MfSets
import InteractingSLE.Spec.Supplement.SB2MoHull
import InteractingSLE.Spec.Supplement.SB2JRight
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# D5's F3 (`hind₁`) in the form SB2(2)'s kernel half consumes (orchestrator adjustment of 01:20 CT)

Packet PROVE-SB2-LCMEAN, round 12. F3 — the mean of the retained union `fill(A ∪ B_{<ℓ})` at the start of B's stage
`ℓ`, by the stage-by-stage induction with terminal limits (supplement p. 632: "Finite induction therefore gives the
optional union identity for the whole staged history") — is proved by the Fable reviewer (REVIEW-FABLE-T14). This
file states it, exactly as the kernel half reads it.

**Consumer.** `Ln.ae_chartTransport_eq_couplingMean_of_stagePullback` (`SB2LnMean`) takes `hind₁`:
almost surely on the stage event, every harmonic representative `w₁` of a local-set mean of `A₁` satisfies
`w₁ + u₀ = G₀ ∘ Φ − χ · lift Φ` on `ℍ ∖ A₁`, for the relative chart `Φ = Ψ ∘ c` (the configuration's chart after B's
stage chart) and `G₀` the bounded harmonic extension of the relative word. Charts of `ℍ ∖ A₁` normalized at `∞`
differ by real translations (`Mo.exists_hullChart_translate`), so it is enough to state it for the canonical hull
chart `Mo.hullChart A₁ 0`, with an existential word (translated in the consumer).

* `stageEvent`: the upper walk launched at `k` and the lower walk launched at `ℓ`;
* `stageMarks`: the retained past, upper walk through `k` with the lower walk before `ℓ` (regularized families);
* **`SB2LowerRetainedMeanStatement`** (REVIEW-FABLE-T14's): in SB2(2)'s setting, for the line family's retained set
  `A₁ = fillVer (stageSet upper k ∪ stageSet (capSpec lower ℓ (−π/2) τ) ℓ)` (`Mf.exists_sb2LowerStageSets`,
  `Ml.exists_sb2LineFamily_cf`), there is a sorted boundary word `β₁`, measurable for the completed retained past,
  such that almost surely on the stage event every harmonic representative `w₁` of every local-set mean of `A₁`
  (centred field) satisfies `w₁ + u₀ = (β₁ ω).mean ∘ mapOut A₁ − χ(κ) · Im(canonDerivLog A₁)` on `ℍ ∖ A₁`.

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

namespace InteractingSLE.Theorem14.SB.Ms

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf Sec4 Supp9B Lx

/-- **The stage event** of B's stage `ℓ` at the upper launch `k`: the upper walk launches at `k` and the lower walk
launches at `ℓ`. -/
def stageEvent (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) : Set Ω :=
  {ω | ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none}

/-- **The retained past at the start of B's stage `ℓ`**: the upper walk through its instruction `k` and the lower walk
before its instruction `ℓ` (regularized families, as in the line family). -/
abbrev stageMarks (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) : MeasurableSpace Ω :=
  pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
    pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ

/-- **Named statement (F3 = `hind₁`; REVIEW-FABLE-T14's, orchestrator adjustment of 01:20 CT): the retained union's
mean at the start of B's stage `ℓ` is a word mean in the canonical hull chart.** In SB2(2)'s setting (the premises of
`Lf.SB2LowerSetting`), for every cap `τ` and every hitting-measurable version `A₁` of the line family's retained set
`fill(A ∪ B_{<ℓ})`, there is a sorted boundary word `β₁`, measurable for the completed retained past, such that for
every local-set mean `g₁` of `A₁` (centred field), almost surely on the stage event, every harmonic representative
`w₁` of `g₁` off `A₁` satisfies `w₁ + u₀ = (β₁ ω).mean ∘ mapOut A₁ − χ(κ) · Im (canonDerivLog A₁)` on `ℍ ∖ A₁`. -/
def SB2LowerRetainedMeanStatement : Prop :=
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
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
    ∀ (ℓ : ℕ) (τ : ℝ≥0∞) (u₀ : ℂ → ℝ), IsBoundedHarmonicExtension b jumps u₀ →
    ∀ A₁ : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A₁ →
      (∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) τ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω) →
      ∃ β₁ : Ω → BoundaryWord,
        Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁ ∧ Measurable β₁ ∧ (∀ ω, (β₁ ω).IsSorted) ∧
        ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₁ (centredField h u₀) P g₁ →
          ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
            ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
              EqOn (fun z => w₁ z + u₀ z)
                (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ ω) 0).2.2 z)
                (H \ A₁ ω)

end InteractingSLE.Theorem14.SB.Ms
