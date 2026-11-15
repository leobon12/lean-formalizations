/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLyGen
import InteractingSLE.Spec.Supplement.SBS3DwBase

/-!
# Successor of `SBLyGen` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SBLyGen` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `SB3InductionGenRLeStatement`;
* `SB2UpperLaunchEntryLAmbLeStatement`;
* `sb3InductionGenRStatement_of_inputsLe`;
* `sb3InductionGenRStatement_of_inputs_dyCoverLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ly

open Lx Lv Lw Sec4 Exist.Staged Exist.StagedLaw

/-- **SB3's stage induction with R95's premise** (`SB.SB3InductionGenStatement` plus `LowerLeftAdmissible`). -/
def SB3InductionGenRLeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ u ψ : ℝ, u ≤ 0 → -(Real.pi / 2) < ψ → ∀ [Fact (ψ ≤ Real.pi / 2)],
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ → (∀ᵐ ω ∂P, 0 < ζ ω) →
      ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ → γ 0 = 0 → range γ = lowerWalkSet κ b jumps E ω →
        ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a

/-! ### SB2(1) in GW1's setting (rulings R94, R96) -/

/-- **Lemma SB2(1), entry form, S1 at launch samples, in GW1's setting** (R94's `Lx.SB2UpperLaunchEntryLStatement`
for boundary data with `LowerLeftAdmissible`: the setting in which PROVE-GW1-EXTREC proves SB2(1)'s clause `m ≤ 0`,
`GW1Ext.ae_launchEntry_nonpos_of_ambient`; without it the clause can fail, R96). -/
def SB2UpperLaunchEntryLAmbLeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ → ∀ [Fact (ψ ≤ Real.pi / 2)],
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      StageS1At κ b jumps P E k u η ζ → SB2UpperConclAt κ b jumps P h E k u ψ η ζ

/-- **SB3's stage induction with R95's premise** from SB2(1) in GW1's setting (S1 at launch samples), SB1, S6,
Theorem 1.3 and the three remaining stage inputs. The general family is regularized (`StagedReg.regFam`, almost surely
the same lower walk); the right additions (I3) are `ae_walkRightAdds_of_bound`, the completability (I4) is
`End.ae_isOneSided_right_real_of_isFlowLine`. -/
theorem sb3InductionGenRStatement_of_inputsLe (hSB2 : SB2UpperLaunchEntryLAmbLeStatement.{u})
    (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hIn : SB3StageInputsRStatement.{u}) : SB3InductionGenRLeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hR u ψ hu hψ _ hL hH η ζ hη hζ
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hR
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    stagedPiecesRegular_of_regular h13 hκ hb (hE' spec hs) (hreg' spec)
  obtain ⟨hpath, hmeas, hmeasT⟩ :=
    hIn κ hκ hκ4 b jumps hb P h hh hadm (StagedReg.regFam E) hE' hR' hreg' u ψ hu hψ hL hH η ζ hη hζ
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => height_lt_of_cumWeightLeft hκ (hadm t ht htJ)
  have hadd := ae_walkRightAdds_of_bound h13 hκ hb hh (hE' _ hspec) (hreg' _) hamb
  have hcomp : ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
      IsOneSided (((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a :=
    (End.ae_isOneSided_right_real_of_isFlowLine hκ hκ4 hη).mono fun _ hω a ha =>
      hω a ha (Icc u 0) fun _ hy => hy.1
  have hordOf : ∀ k, StageS1At κ b jumps P (StagedReg.regFam E) k u η ζ →
      StageOrderingAt κ ψ b jumps P h (StagedReg.regFam E) η ζ k u := fun k hS1 =>
    stageOrderingAt_of_concl hSB1 hS6 h13 hκ hκ4 hE' k hψ hL hH
      (hSB2 κ hκ hκ4 b jumps hb P h hh hadm (StagedReg.regFam E) hE' hR' k u ψ hu hψ hL hH η ζ hη hS1)
  filter_upwards [ae_sb3_of_inputsO hSB1 hS6 h13 hκ hκ4 hb hh hE' hR' (hreg' _) hu hψ hL hH hη hζ hordOf
    hcomp hpath hadd hmeas hmeasT, hrun _ hspec] with ω hω hrω γ hγ hγ0 hrange
  refine hω γ hγ hγ0 (hrange.trans ?_)
  exact (StagedReg.physSet_eq_of_run_eq (hrω _)).symm

/-- `sb3InductionGenRStatement_of_inputsLe` with SB1 and S6 discharged by the landed `W5Assembly` results. -/
theorem sb3InductionGenRStatement_of_inputs_dyCoverLe (hSB2 : SB2UpperLaunchEntryLAmbLeStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hIn : SB3StageInputsRStatement.{u}) : SB3InductionGenRLeStatement.{u} :=
  sb3InductionGenRStatement_of_inputsLe hSB2 (W5Assembly.sb1Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀)
    (W5Assembly.s6Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀) h13 hIn

/-! ### The premise in the counterflow setting -/

/-! ### The counterflow forms (ruling R96) -/

end InteractingSLE.Theorem14.SB.Ly
