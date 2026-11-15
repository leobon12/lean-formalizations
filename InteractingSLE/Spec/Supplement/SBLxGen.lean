/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLxFinal
import InteractingSLE.Spec.Supplement.SBLeafSB3

/-!
# SB3's induction statement from SB2(1) and the stage inputs

Packet PROVE-T14-SBLEAVES3 (second round). `sb3InductionGenStatement_of_inputs`: the leaf `hSB3`
(`SB.SB3InductionGenStatement`) from SB2(1) in entry form at launch samples (`SB2UpperLaunchEntryLStatement`, F8 on
R91's form), Theorems 1.2–1.3 with the small-gap fibre cover (for SB1 and S6), and the stage inputs
`SB3StageInputsStatement` (for families regular at every sample; the general family is regularized by
`StagedReg.regFam`, which has almost surely the same lower walk).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lx

open Lv Lw Sec4 Exist.Staged Exist.StagedLaw

/-- **The stage inputs of SB3's induction** (named open inputs, for staged families regular at every sample):
the upper flow's prefixes have proper completions (S1 for the bridge; SB3: "the upper flow can be completed on its
left"); every retained prefix after the first stage is the image of a path with finite fibres from the upper seed;
the walk's connectors and zero-lifetime pieces add only real points `≥ 0` (right records: SB3, "the lower endpoint
`q` is a new right record. Adding the next interval `[q, w]`"); the stage and truncation claim events are
null-measurable (supplement p. 577: S1 events are universally measurable). -/
def SB3StageInputsStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ spec j ω, IsRegularDriver (E spec j ω)) →
    ∀ u ψ : ℝ, u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ → (∀ᵐ ω ∂P, 0 < ζ ω) →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a) ∧
      (∀ k, 1 ≤ k → ∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω →
        ∃ p : ℝ → ℂ, IsPrefixPath p u (lowerPrefix κ b jumps E k u ω)) ∧
      (∀ᵐ ω ∂P, WalkRightAdds κ b jumps E ω) ∧
      (∀ k, NullMeasurableSet {ω | SB3StageClaim κ b jumps E k u η ζ ω} P) ∧
      ∀ k, NullMeasurableSet {ω | SB3TruncClaim κ b jumps E k u η ζ ω} P

/-- **SB3's stage induction** (`hSB3`) from SB2(1) at launch samples, SB1, S6, Theorem 1.3 and the stage inputs. -/
theorem sb3InductionGenStatement_of_inputs (hSB2 : SB2UpperLaunchEntryLStatement.{u}) (hSB1 : SB1Statement.{u})
    (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) (hIn : SB3StageInputsStatement.{u}) :
    SB3InductionGenStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR u ψ hu hψ hL hH η ζ hη hζ
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hR
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    stagedPiecesRegular_of_regular h13 hκ hb (hE' spec hs) (hreg' spec)
  obtain ⟨hcomp, hpath, hadd, hmeas, hmeasT⟩ :=
    hIn κ hκ hκ4 b jumps hb P h hh (StagedReg.regFam E) hE' hR' hreg' u ψ hu hψ hL hH η ζ hη hζ
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  filter_upwards [ae_sb3_of_inputs hSB2 hSB1 hS6 h13 hκ hκ4 hb hh hE' hR' (hreg' _) hu hψ hL hH hη hζ
    hcomp hpath hadd hmeas hmeasT, hrun _ hspec] with ω hω hrω γ hγ hγ0 hrange
  refine hω γ hγ hγ0 (hrange.trans ?_)
  exact (StagedReg.physSet_eq_of_run_eq (hrω _)).symm

/-- `sb3InductionGenStatement_of_inputs` with SB1 and S6 discharged by the landed `W5Assembly` results. -/
theorem sb3InductionGenStatement_of_inputs_dyCover (hSB2 : SB2UpperLaunchEntryLStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hIn : SB3StageInputsStatement.{u}) : SB3InductionGenStatement.{u} :=
  sb3InductionGenStatement_of_inputs hSB2 (W5Assembly.sb1Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀)
    (W5Assembly.s6Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀) h13 hIn

end InteractingSLE.Theorem14.SB.Lx
