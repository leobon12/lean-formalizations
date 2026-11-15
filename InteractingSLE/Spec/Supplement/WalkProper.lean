/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ParamProof
import InteractingSLE.Spec.Supplement.GW3SidedProofWalk

/-!
# Theorem 1.4's walks: the left walk's proper parametrization, R51 reduction

Packet PROVE-T14-GW9. Lemma GW1 (supplement p. 618): "There is a field-determined continuous injective proper curve
`R` from `x` to `y` […] Reflection gives the left boundary walk `L` at angle `+π/2`." PROVE-T14-GW8 recorded the left
walk's statement as the named input `GW3SidedProof.LeftWalkProperRegStatement` (R51 form: staged families that are
`StagedPiecesRegular`). This file reduces it, exactly as PROVE-T14-GW1X did for the right walk
(`GW1X.gw1ParamR51Statement_of_everyReg`), to the same statement for staged families whose drivers are regular at every
sample (`LeftWalkParamEveryRegStatement`, the left mirror of `GW1X.GW1ParamEveryRegStatement`): regularize the family
(`StagedReg.regFam`, a staged history regular at every sample with almost surely the same runs), so the left walk's
physical set is almost surely unchanged (`StagedReg.physSet_eq_of_run_eq`).

GW1's simple-curve core itself (for either walk) is not proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.WalkProper

open Exist Exist.StagedLaw StagedReg

/-- **GW1's parametrization of the left walk for staged families regular at every sample** (the left mirror of
`GW1X.GW1ParamEveryRegStatement`): almost surely the physical set of the left walk (angle `+π/2`, continuing left) is
the range of a proper simple curve in `closure ℍ` from `0`. -/
def LeftWalkParamEveryRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec k ω, Staged.IsRegularDriver (E spec k ω)) →
      ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧
        range γ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)

/-- **R51 reduction for the left walk**: its parametrization for families regular at every sample gives
`GW3SidedProof.LeftWalkProperRegStatement` (the regularized family has almost surely the same left walk). -/
theorem leftWalkProperRegStatement_of_everyReg (hG : LeftWalkParamEveryRegStatement.{u}) :
    GW3SidedProof.LeftWalkProperRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR
  obtain ⟨hE', hreg', hrun⟩ := regFam_spec hb hE hR
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (regFam E) hE' hreg',
    hrun _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)] with ω hγ hrω
  obtain ⟨γ, hγ, hγ0, hγL⟩ := hγ
  exact ⟨γ, hγ, hγ0, hγL.trans (physSet_eq_of_run_eq (hrω _))⟩

end InteractingSLE.Theorem14.WalkProper
