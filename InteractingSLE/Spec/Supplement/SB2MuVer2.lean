/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuInt

/-!
# D5's F2b, amended: the per-stage relative version with the true lifetime and (I4) at the version level

Packet PROVE-SB2-LCMEAN, round 13. Amends the landed `Ms.SB2LowerStageVersionStatement` (round 12; not yet worked on
by PROVE-AUX61-NOJUMP) after building its consumer (`Mu.ae_isStopDrvMatch_of_lines`, `Mu.isDriverCodeMatch_of_stops`):

* the landed statement pins `relLife` only through the stops (`V m ↑ relLife`), so a version truncated at half the
  true lifetime satisfies it; the identification with `EL`'s lifetime needs every B-time before B's death to come
  before some stop;
* with `relLife` the true lifetime, an arbitrary word `β₁` would make `Λ ≤ thr` false (a word with a near threshold
  has a small `thr`); `β₁` is therefore F3's retained word (its mean identity is a hypothesis), as SB2(1)'s stops used
  the actual launch word;
* (I4) at the version level, D10 step 1 mirrored;
* the version's chart is the hull chart with offset `x₀`, so its word is F3's word shifted by `x₀`
  (`BoundaryWord.shiftW`; F3 and the retained kernel law use offset `0`).

**`Mu.SB2LowerStageVersionStatement2`** replaces the landed statement as NOJUMP's target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mu

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms

/-- **Named statement (F2b, amended; PROVE-AUX61-NOJUMP's, ruling R120/D5)**: `Ms.SB2LowerStageVersionStatement` with
the word `β₁` the retained word (F3's mean identity at the stage start is a hypothesis, as SB2(1)'s stops used the
actual launch word), and two more clauses on the versions:
* **the stops reach every time of B's piece**: before B's lifetime, every B-time is before some stop (this pins
  `relLife` as the true relative lifetime; without it a version truncated at half the lifetime satisfies every field);
* **every stop is below the threshold on the whole type cell** (SB2(1)'s `SB2LineVersionS.V_le_thr`; the landed
  `Λ_le` covers only the seed-admissible part, and the cell-wide bound gives seed admissibility since stops are
  positive);
* **(I4) at the version level** (D10 step 1 mirrored, "the flow ends at a bad point at a finite lifetime"): almost
  surely on every admissible type cell with a finite relative lifetime, for every continuous driver `Wc` that
  continues the frozen drivers at that sample, the threshold time of the type's force points under `Wc` is at most the
  relative lifetime. -/
def SB2LowerStageVersionStatement2 : Prop :=
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
    ∀ (ψ : ℝ) (β₁ : Ω → BoundaryWord) (types : Set WordType),
      Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁ → (∀ ω, (β₁ ω).IsSorted) → types.Countable →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
      (∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
              (H \ A₁ 0 ω)) →
    ∃ (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (relLife : Ω → ℝ≥0∞) (F : Set Ω),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K ∧ (∀ ω, IsCompact (K ω)) ∧
      (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧ (∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) ∧
      Measurable[lineFiltC P 𝓖 0] x₀ ∧ MeasurableSet[lineFiltC P 𝓖 0] F ∧
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ≤ ℓ ∧ 0 < relLife ω)) ∧
      ((∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types) →
        ∃ S : StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
          (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
          (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife,
          (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F →
            (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
            ∃ m, (S.ver m).a t ω < S.V m ω) ∧
          (∀ m, ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
            S.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver m).W
              (cellXL κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
              (cellXR κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω) ∧
          ∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
            ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w → relLife ω < ⊤ →
              (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
              FCDet.thr (typedRhoL w) (typedRhoR w) Wc (cellXL κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
                (cellXR κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω ≤ relLife ω)

end InteractingSLE.Theorem14.SB.Mu
