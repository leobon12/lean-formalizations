/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KSplit
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DxKAmb
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen

/-!
# Successor of `SB2KSplit` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SB2KSplit` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `SB2DriverLinkAmbLeStatement`;
* `sb2RelCoreAmbRegSuccStatement_of_partsLe`;
* `sb2UpperLaunchEntryLAmbStatement_of_partsLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4 Exist.Staged

/-- **Named input: SB2(1)'s clauses (1) and (3) at the launches after the first, in GW1's ambient setting** (K2's
conditional flow-line driver in the launch chart recentred at its entry, and the remainder link). -/
def SB2DriverLinkAmbLeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    Ly.LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (j : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec j ω)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ → ∀ [Fact (ψ ≤ Real.pi / 2)],
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, Lx.LowerLaunch κ b jumps E (k + 1) ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (lowerPrefix κ b jumps E (k + 1) u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) P (launchSet κ b jumps E (k + 1)) h
        (fun ω => (launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω)) bc jc W ζr ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) ω₀),
          IsRemainderLink (launchChart κ b jumps E (k + 1) ω₀) (η ω) (ζ ω)
            (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
            (fun t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E (k + 1) u ω₀) (ζr ω))

/-- **The ambient input from its two parts.** -/
theorem sb2RelCoreAmbRegSuccStatement_of_partsLe (hw : SB2ActiveWordAmbStatement.{u})
    (hd : SB2DriverLinkAmbLeStatement.{u}) : SB2RelCoreAmbRegSuccLeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hER hreg k u ψ hu hψ _ hL hH η ζ hη hS1
  obtain ⟨bc, jc, W, ζr, h1, h3⟩ := hd κ hκ hκ4 b jumps hb P h hh hadm E hE hER hreg k u ψ hu hψ hL hH η ζ hη hS1
  exact ⟨bc, jc, W, ζr, h1, hw κ hκ hκ4 b jumps hb P h hh hadm E hE hER hreg k u hu, h3⟩

/-- **SB2(1) in the ambient form SB3 consumes** (`Ly.SB2UpperLaunchEntryLAmbLeStatement`), from Theorem 1.3, the active
word and the driver with its link at the launches after the first. -/
theorem sb2UpperLaunchEntryLAmbStatement_of_partsLe (h13 : Exist.Theorem13Statement.{u})
    (hw : SB2ActiveWordAmbStatement.{u}) (hd : SB2DriverLinkAmbLeStatement.{u}) :
    Ly.SB2UpperLaunchEntryLAmbLeStatement.{u} :=
  sb2UpperLaunchEntryLAmbStatement_of_succLe h13 (sb2RelCoreAmbRegSuccStatement_of_partsLe hw hd)

end InteractingSLE.Theorem14.SB.Lv
