/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4ProofFrontier
import InteractingSLE.Spec.Supplement.SB3ProofTop

/-!
# Theorem SB4's clauses, Corollary SB5, SB and Lemma SB3 under ruling R51

Packet PROVE-T14-SB6. The version-2 frontier wrapper `SB.boundaryWalks_frontiers_of_openReg` (PROVE-T14-SB5) still
consumes the **unregularized** SB4 clauses `SB4DistinctSeedStatement` and `SB4InitialArcStatement`. Both are pathwise
statements about the physical sets of staged families (`ExplState.physSet`) quantified over every family satisfying
`IsStagedHistory`; by R51 such families may have irregular later pieces on a set of positive outer measure, so these
clauses are not expected to be provable. The source's walks and schedules are actual continuous curves (p. 136), which
is R51's `StagedPiecesRegular`. This file restates the SB chain with that hypothesis (placed right after `hE`, as in
`SBFrontierRegStatement`) and reruns its deterministic and countable-union proofs:

* `SB4DistinctSeedRegStatement`, `SB4InitialArcRegStatement`, `SB4RegStatement`, `SB5RegStatement`, `SBRegStatement`,
  and for Lemma SB3 `GW1ParamRegStatement`, `SB3InductionRegStatement`, `SB3RegStatement` — each the named statement
  with R51's hypothesis; every unregularized statement implies its regularized form (`*_of_unreg`);
* `sb4RegStatement_of_distinctSeed`, `sb5RegStatement_of_inputs`, `sbRegStatement_of_sb4_sb5`,
  `sbFrontierRegStatement_of_sbReg`, `sbFrontierRegStatement_of_sb4Reg` (the proofs of the version-1 chain with `hreg`);
* `sb3RegStatement_of_param_induction` (Lemma SB3 from GW1's parametrization, its stage induction and the proved
  final certificate `sb3TopologyStatement`);
* **`boundaryWalks_frontiers_of_openReg2`** — the version-2 frontier wrapper of `boundaryWalks_frontiers_of_openReg`
  with the two regularized SB4 clauses in place of the unregularized ones.

Conditional helpers with distinct names; none is a provider.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

open Sec4
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### The regularized statements -/

/-- **Theorem SB4, distinct-seed version, for regular families** (`SB4DistinctSeedStatement` with R51's hypothesis
`StagedPiecesRegular` on every boundary-continued family). -/
def SB4DistinctSeedRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      (∀ u ≤ 0, (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨u, true, scheduleProgram 0 l⟩
            (fun k => E ⟨u, true, scheduleProgram 0 l⟩ k ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      (∀ v, 0 ≤ v → (∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩
            (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅)

/-- **Theorem SB4, same-connector assertion on the initial forced arc, for regular families**
(`SB4InitialArcStatement` with R51's hypothesis). -/
def SB4InitialArcRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ v : ℝ, 0 < v →
      rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ →
      (∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      ∀ᵐ ω ∂P,
        ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅

/-- **Theorem SB4, common seed, for regular families** (`SB4Statement` with R51's hypothesis). -/
def SB4RegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      ((∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
            (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      ((∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
            (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅)

/-- **Corollary SB5 for regular families** (`SB5Statement` with R51's hypothesis). -/
def SB5RegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ v : ℝ, 0 < v →
      rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ →
      (∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) →
      ∀ᵐ ω ∂P,
        ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ∩
            rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅ ∧
          ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩
              (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ∩
            leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅

/-- **The sewn-barrier input SB for regular families** (`SBStatement` with R51's hypothesis). -/
def SBRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable → ∀ Q : Set ℝ≥0, Q.Countable →
      ∀ᵐ ω ∂P,
        boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∩
            rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅ ∧
          boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∩
            leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅

/-- **GW1's parametrization for regular families** (`GW1ParamStatement` with R51's hypothesis): almost surely the
physical set of the lower walk is the range of a proper simple curve in `closure ℍ` from `0`. -/
def GW1ParamRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ range γ = lowerWalkSet κ b jumps E ω

/-- **SB3's stage induction for regular families** (`SB3InductionStatement` with R51's hypothesis). -/
def SB3InductionRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ u ψ : ℝ, u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ → (∀ᵐ ω ∂P, 0 < ζ ω) →
      ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ → γ 0 = 0 → range γ = lowerWalkSet κ b jumps E ω →
        ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a

/-- **Lemma SB3 for regular families** (`SB3Statement` with R51's hypothesis). -/
def SB3RegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ u ψ : ℝ, u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ → (∀ᵐ ω ∂P, 0 < ζ ω) →
      ∀ᵐ ω ∂P, η ω '' {t | (t : ℝ≥0∞) ≤ ζ ω} ∩
        rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅

/-! ### Every unregularized statement implies its regularized form -/

theorem sb4DistinctSeedRegStatement_of_unreg (h : SB4DistinctSeedStatement.{u}) : SB4DistinctSeedRegStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h' hh W' ζ' hcf hζ' E hE _ =>
    h κ hκ hκ4 b jumps hb P h' hh W' ζ' hcf hζ' E hE

theorem sb4InitialArcRegStatement_of_unreg (h : SB4InitialArcStatement.{u}) : SB4InitialArcRegStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h' hh W' ζ' hcf hζ' E hE _ =>
    h κ hκ hκ4 b jumps hb P h' hh W' ζ' hcf hζ' E hE

theorem gw1ParamRegStatement_of_unreg (h : GW1ParamStatement.{u}) : GW1ParamRegStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h' hh W' ζ' hcf hζ' E hE _ =>
    h κ hκ hκ4 b jumps hb P h' hh W' ζ' hcf hζ' E hE

theorem sb3InductionRegStatement_of_unreg (h : SB3InductionStatement.{u}) : SB3InductionRegStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h' hh W' ζ' hcf hζ' E hE _ =>
    h κ hκ hκ4 b jumps hb P h' hh W' ζ' hcf hζ' E hE

/-! ### The chain -/

/-- **Theorem SB4, common seed, from its distinct-seed version, for regular families** (as
`sb4Statement_of_distinctSeed`: the bridge `(0, 0)` is empty). -/
theorem sb4RegStatement_of_distinctSeed (hDS : SB4DistinctSeedRegStatement.{u}) : SB4RegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  have H := hDS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun hθ => H.1 0 le_rfl hθ forall_mem_Ioo_self fun _ _ => forall_mem_Ioo_self,
    fun hθ => H.2 0 le_rfl hθ forall_mem_Ioo_self fun _ _ => forall_mem_Ioo_self⟩

/-- **Corollary SB5 for regular families** (the proof of `sb5Statement_of_inputs` with `hreg`). -/
theorem sb5RegStatement_of_inputs (hGW0 : GW0.GW0ForwardStatement.{u}) (hIA : SB4InitialArcRegStatement.{u})
    (hDS : SB4DistinctSeedRegStatement.{u}) : SB5RegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl hθ
  have h41 : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ := fun p hp q hq =>
    sb41_of_mem_Ioo hκ hκ4 (hθ p hp) (hθ q hq)
  have hlower := hIA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41
    fun p hp => ⟨(hθ p hp).1, (hθ p hp).2.le⟩
  have hupper := (hDS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41).2 v hv.le
    (fun p hp => ⟨(hθ p hp).1.le, (hθ p hp).2⟩)
    (fun x hx hxJ => (sb51_of_counterflow hGW0 hκ hκ4 hb hh hcf hζ' hlow0 hlow hx hxJ le_rfl).1)
    (fun p hp x hx hxJ => Or.inl
      (sb51_of_counterflow hGW0 hκ hκ4 hb hh hcf hζ' hlow0 hlow hx hxJ (hθ p hp).2.le).2)
  filter_upwards [hlower, hupper] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **SB from SB4 and SB5, for regular families** (the proof of `sbStatement_of_sb4_sb5` with `hreg`). -/
theorem sbRegStatement_of_sb4_sb5 (h4 : SB4RegStatement.{u}) (h5 : SB5RegStatement.{u}) : SBRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg Θ hΘ hΘc Q hQc
  have hS := countable_setOf_isSchedule hΘc hQc
  have hV := countable_lowerArcRoots κ b jumps
  have hA := (ae_ball_iff hS).2 fun l (hl : l ∈ {l | IsSchedule Θ Q l}) => by
    have hang : ∀ p ∈ l, p.1 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := fun p hp => hΘ (hl.1 p hp).1
    obtain ⟨hR, hL⟩ := h4 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl.2
      fun p hp q hq => sb41_of_mem_Ioo hκ hκ4 (hang p hp) (hang q hq)
    exact (hR fun p hp => ⟨(hang p hp).1, (hang p hp).2.le⟩).and
      (hL fun p hp => ⟨(hang p hp).1.le, (hang p hp).2⟩)
  have hB := (ae_ball_iff hV).2 fun v (hv : v ∈ lowerArcRoots κ b jumps) =>
    (ae_ball_iff hS).2 fun l (hl : l ∈ {l | IsSchedule Θ Q l}) => by
      obtain ⟨hv0, h0, hjv⟩ := lowArc_of_mem_lowerArcRoots hv
      exact h5 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v hv0 h0 hjv l hl.2
        fun p hp => hΘ (hl.1 p hp).1
  filter_upwards [hA, hB] with ω hA hB
  constructor
  · refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hzF, hzR⟩ := hz
    simp only [boundaryLightConeFamily, mem_union, mem_iUnion, mem_image] at hzF
    rcases hzF with ⟨l, hl, hzl⟩ | ⟨v, hv, ⟨x, -, rfl⟩ | ⟨l, hl, hzl⟩⟩
    · exact (eq_empty_iff_forall_notMem.1 (hA l hl).1) z ⟨hzl, hzR⟩
    · exact ofReal_notMem_H x hzR.1.1
    · exact (eq_empty_iff_forall_notMem.1 (hB v hv l hl).1) z ⟨hzl, hzR⟩
  · refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hzF, hzL⟩ := hz
    simp only [boundaryLightConeFamily, mem_union, mem_iUnion, mem_image] at hzF
    rcases hzF with ⟨l, hl, hzl⟩ | ⟨v, hv, ⟨x, -, rfl⟩ | ⟨l, hl, hzl⟩⟩
    · exact (eq_empty_iff_forall_notMem.1 (hA l hl).2) z ⟨hzl, hzL⟩
    · exact ofReal_notMem_H x hzL.1.1
    · exact (eq_empty_iff_forall_notMem.1 (hB v hv l hl).2) z ⟨hzl, hzL⟩

/-- **The frontier input for regular families from GW2 and SB for regular families** (the proof of
`sbFrontierRegStatement_of_inputs` with the regularized SB). -/
theorem sbFrontierRegStatement_of_sbReg (hGW2 : GW2LightConeStatement.{u}) (hSB : SBRegStatement.{u}) :
    SBFrontierRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hΘ : Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ) ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    inter_subset_left
  have hΘc : (Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ)).Countable :=
    (countable_range _).mono inter_subset_right
  have hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆
      closure (Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ)) :=
    Dense.open_subset_closure_inter Rat.denseRange_cast isOpen_Ioo
  obtain ⟨Q, hQc, -, -, hQ⟩ := hGW2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hΘ hΘc hΘd
  filter_upwards [hQ E hE, hSB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg _ hΘ hΘc Q hQc,
    GW1P.gw1ProperRegStatement κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω hω hsb hpr
  rw [← hω]
  refine ⟨closure_inter_eq_empty (isOpen_rightSideOf hpr.1) ?_, closure_inter_eq_empty (isOpen_leftSideOf hpr.2) ?_⟩
  · rw [union_inter_distrib_right, hsb.1, empty_union]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hz0, hzR⟩ := hz
    rw [mem_singleton_iff] at hz0
    subst hz0
    exact ofReal_notMem_H 0 (by simpa using hzR.1.1)
  · rw [union_inter_distrib_right, hsb.2, empty_union]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hz0, hzL⟩ := hz
    rw [mem_singleton_iff] at hz0
    subst hz0
    exact ofReal_notMem_H 0 (by simpa using hzL.1.1)

/-- **The frontier input for regular families from SB4's two regularized clauses** (GW2, GW0's forward implication). -/
theorem sbFrontierRegStatement_of_sb4Reg (hGW2 : GW2LightConeStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hDS : SB4DistinctSeedRegStatement.{u}) (hIA : SB4InitialArcRegStatement.{u}) : SBFrontierRegStatement.{u} :=
  sbFrontierRegStatement_of_sbReg hGW2
    (sbRegStatement_of_sb4_sb5 (sb4RegStatement_of_distinctSeed hDS) (sb5RegStatement_of_inputs hGW0 hIA hDS))

/-- **Lemma SB3 for regular families** from GW1's parametrization and SB3's stage induction (both for regular
families) and the proved final certificate `sb3TopologyStatement` (the proof of `sb3Statement_of_inputs`). -/
theorem sb3RegStatement_of_param_induction (hP : GW1ParamRegStatement.{u}) (hI : SB3InductionRegStatement.{u}) :
    SB3RegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg u ψ hu hψ hL hH η ζ hη hζ
  filter_upwards [hP κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hI κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg u ψ hu hψ hL hH η ζ hη hζ,
    IsFlowLine.ae_seed_continuousOn hη] with ω ⟨γ, hγ, hγ0, hγR⟩ hS ⟨h0, hc⟩
  have := sb3TopologyStatement γ (η ω) (ζ ω) u hγ hγ0 hu h0 hc (hS γ hγ hγ0 hγR)
  rw [hγR] at this
  exact this

/-! ### The version-2 frontier wrapper with the regularized SB4 clauses -/

/-- **Theorem 1.4, frontiers, version 2** (`IsCenteredCounterflowDriver.boundaryWalks_frontiers`, R51), provider
shape, from the inputs of `boundaryWalks_frontiers_of_openReg` with SB4's two clauses **for regular families**
(`SB4DistinctSeedRegStatement`, `SB4InitialArcRegStatement`), which the source proves (its walks and schedules are
continuous curves); the version-2 anchor's `hreg` serves them (conditional helper; not the provider). -/
theorem boundaryWalks_frontiers_of_openReg2 (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u})
    (hC0 : GW2Cone.GW2ScheduleContainmentStatement.{u}) (hCv : GW2Cone.GW2ArcScheduleContainmentStatement.{u})
    (hEx : GW2Cone.GW2TipExhaustionStatement.{u}) (hGW2a : GW2aContainmentStatement.{u})
    (hDS : SB4DistinctSeedRegStatement.{u}) (hIA : SB4InitialArcRegStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption)
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec) := by assumption) :
    ∀ᵐ ω ∂P,
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅) ∧
      (interior (((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω)) = ∅ →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
          (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤) :=
  boundaryWalks_frontiers_of_inputsReg hGW2a
    (sbFrontierRegStatement_of_sb4Reg (Wire.gw2LightConeStatement_of_open5 h13 h13₀ hBR6 hC0 hCv hEx)
      (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hDS hIA)
    (gw6Statement_of_gw2a hGW2a GW1.gw1FirstThresholdStatement) hκ hκ4 b jumps hb hh hcf hζ' E hE hreg

end SB

end Theorem14

end InteractingSLE
