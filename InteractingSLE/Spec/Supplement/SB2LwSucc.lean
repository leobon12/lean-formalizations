/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwZero

/-!
# SB2(2): the law half reduced to the later launches; R99's target from Theorem 1.3 and that input

Packet PROVE-T14-SB2LOW (ruling R99). With the word half PROVED (`SB2LwFinal`) and the law half PROVED at the first
launch (`SB2LwZero`), R99's target `Lz.SB2LowerLaunchEntryAdmStatement` needs only the law half at the later launches
`k + 1` (`SB2LowerLawSuccStatement`, the verbatim `Lz.SB2LowerLawStatement` at `k + 1`):

* **`sb2LowerLawStatement_of_succ`**: `Lz.SB2LowerLawStatement` from Theorem 1.3 and `SB2LowerLawSuccStatement`;
* **`sb2LowerLaunchEntryAdmStatement_of_succ`**: R99's target from Theorem 1.3 and `SB2LowerLawSuccStatement`.

R48: Theorem 1.3 appears only as a hypothesis; this serves Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lh

open Lx Lu Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw

/-- **SB2(2)'s law half at the later launches** (named input): `Lz.SB2LowerLawStatement` with the launch index
`k + 1` (the first launch `k = 0` is `sb2LowerLaw_zero`). -/
def SB2LowerLawSuccStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
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
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l (k + 1) →
        upperPrefix κ b jumps E u l (k + 1) ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1 + 1)).2.2.2.1 (k + 1) =
            some (c, θ) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData
            (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) (k + 1)) ω₀) h' b' jumps' →
          ∀ m : ℝ, m = -upperEntry κ b jumps E u l (k + 1) ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
            IsStagedHistory κ (affData 1 m b') (affJumps 1 m jumps')
              (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) (k + 1)) ω₀)
              (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' jumps' m) EL ∧
            StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m jumps')
              (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) (k + 1)) ω₀)
              (relLowerSpec b' jumps' m) EL ∧
            (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) (k + 1)) ω₀),
              WalkRightAdds κ (affData 1 m b') (affJumps 1 m jumps') (fun _ => EL) ω) ∧
            ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) (k + 1)) ω₀),
              lowerWalkSet κ b jumps E ω ∩ (H \ fillH (upperPrefix κ b jumps E u l (k + 1) ω)) ⊆
                  relPhysSet κ (affData 1 m b') (affJumps 1 m jumps') (c.recenter (-m))
                    (relLowerSpec b' jumps' m) (fun j => EL j ω) ∧
                relPhysSet κ (affData 1 m b') (affJumps 1 m jumps') (c.recenter (-m))
                    (relLowerSpec b' jumps' m) (fun j => EL j ω) ⊆
                  lowerWalkSet κ b jumps E ω

/-- **SB2(2)'s law half from its later launches** (the first launch is `sb2LowerLaw_zero`). -/
theorem sb2LowerLawStatement_of_succ (h13 : Exist.Theorem13Statement.{u}) (h130 : Exist.Theorem13Statement.{0})
    (hs : SB2LowerLawSuccStatement.{u}) : Lz.SB2LowerLawStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER x₀ l k hx₀ hlp hlθ hL hleft
  cases k with
  | zero =>
    exact sb2LowerLaw_zero h13 (BR3Ref.gw0ForwardStatement_of_theorem13 h130) hκ hκ4 hb hh hcf hζ' hE hER l hx₀
  | succ k => exact hs κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER x₀ l k hx₀ hlp hlθ hL hleft

/-- **R99's target from Theorem 1.3 and SB2(2)'s law half at the later launches.** -/
theorem sb2LowerLaunchEntryAdmStatement_of_succ (h13 : Exist.Theorem13Statement.{u})
    (h130 : Exist.Theorem13Statement.{0}) (hs : SB2LowerLawSuccStatement.{u}) :
    Lz.SB2LowerLaunchEntryAdmStatement.{u} :=
  sb2LowerLaunchEntryAdmStatement_of_law h130 (sb2LowerLawStatement_of_succ h13 h130 hs)

end InteractingSLE.Theorem14.SB.Lh
