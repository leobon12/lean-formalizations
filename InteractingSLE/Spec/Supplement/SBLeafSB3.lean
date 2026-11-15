/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4Clauses

/-!
# Lemma SB3's stage induction without the ambient counterflow

Packet PROVE-T14-SBTAIL. Lemma SB3 (specification p. 633, `source/spec/p625-671.md` L151–L167)
compares one constant-angle flow with the completed lower walk of the same field. Its statement
and proof mention no counterflow line. The landed `SB3InductionRegStatement` carries the
Theorem 1.4 counterflow binder `(W', ζ')` of its setting. SB4's switch step applies SB3 to a
*conditional* field read in a relative chart, where no counterflow of infinite lifetime is
available without a separate admissibility argument. This file states the induction exactly as
the source does (the same binders and conclusion, minus the unused counterflow) and records the
trivial implication to the landed form. It is an open source statement, not a proof of SB3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)

universe u

namespace InteractingSLE.Theorem14.SB

open Sec4

/-- **SB3's stage induction, source form** (`SB3InductionRegStatement` without the Theorem 1.4
counterflow binder): a constant flow of angle `ψ > −π/2` from `u ≤ 0`, with the hybrid word of SB1
on `(u, 0)`, has the one-sided completion S1 against every prefix of the completed lower walk
(with the bridge `[u, 0]` retained). -/
def SB3InductionGenStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
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

/-- The source form implies the landed form (the counterflow binder is simply not used). -/
theorem sb3InductionRegStatement_of_gen (h : SB3InductionGenStatement.{u}) :
    SB3InductionRegStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h' hh _ _ _ _ E hE hreg u ψ hu hψ hL hH η ζ hη hζ =>
    h κ hκ hκ4 b jumps hb P h' hh E hE hreg u ψ hu hψ hL hH η ζ hη hζ

/-- Lemma SB3 for regular families from GW1's parametrization and the source-form induction. -/
theorem sb3RegStatement_of_param_gen (hP : GW1ParamRegStatement.{u})
    (hI : SB3InductionGenStatement.{u}) : SB3RegStatement.{u} :=
  sb3RegStatement_of_param_induction hP (sb3InductionRegStatement_of_gen hI)

end InteractingSLE.Theorem14.SB
