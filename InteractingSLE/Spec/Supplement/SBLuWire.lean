/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLuMeas
import InteractingSLE.Spec.Supplement.SBLzRun

/-!
# SB3 with the measurability inputs discharged

Packet PROVE-T14-SBLEAVES6. With `sb3StageMeasCfStatement` (SBLuMeas):

* `sb3InductionRegStatement_of_thms''`: SB3's induction in Theorem 1.4's counterflow setting
  (`SB.SB3InductionRegStatement`, R96) from SB2(1) in that setting, Theorems 1.2–1.3 and the small-gap fibre cover;
* `SB3StagePathRStatement` (the one remaining stage input (I5) of the amended SB3: retained prefixes at launches are
  paths), `sb3StageInputsRStatement_of_path` (the two measurability clauses of `Ly.SB3StageInputsRStatement` are
  proved), `sb3InductionGenRStatement_of_path`: R95's amended SB3 (`Ly.SB3InductionGenRStatement`, Theorem 1.4's
  `hSB3`) from SB2(1) (ambient form), Theorems 1.2–1.3, the fibre cover and (I5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.LuM

open Lx Lv Lw Sec4 Exist.Staged Exist.StagedLaw

/-- **SB3's induction in Theorem 1.4's counterflow setting** (`SB.SB3InductionRegStatement`, R96) from SB2(1) in that
setting, Theorems 1.2–1.3 and the small-gap fibre cover (SB1/S6): the measurability inputs (I2), (I2′) are
`sb3StageMeasCfStatement`, the run fact is PROVE-T14-SBLEAVES5's. -/
theorem sb3InductionRegStatement_of_thms'' (hSB2 : Ly.SB2UpperLaunchEntryLCfStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    SB3InductionRegStatement.{u} :=
  Lz.sb3InductionRegStatement_of_thms' hSB2 h12 h13 h12₀ h13₀ hDy hDy₀ sb3StageMeasCfStatement

/-- **The remaining stage input (I5) of the amended SB3** (`Ly.SB3StageInputsRStatement` without its two
measurability clauses, which are proved): at every launch `k ≥ 1` of the lower walk the retained prefix (with the
bridge `[u, 0]`) is the image of a path with finite fibres from `u`. -/
def SB3StagePathRStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    Ly.LowerLeftAdmissible κ b jumps →
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
      ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω →
        ∃ p : ℝ → ℂ, IsPrefixPath p u (lowerPrefix κ b jumps E k u ω)

/-- **The stage inputs of the amended SB3 reduce to (I5)**: the two measurability clauses are proved. -/
theorem sb3StageInputsRStatement_of_path (hPath : SB3StagePathRStatement.{u}) :
    Ly.SB3StageInputsRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hR hreg u ψ hu hψ hL hH η ζ hη hζ
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  refine ⟨hPath κ hκ hκ4 b jumps hb P h hh hadm E hE hR hreg u ψ hu hψ hL hH η ζ hη hζ, fun k => ?_, fun k => ?_⟩
  · exact (nullMeasurableSet_claims hb (hE _ hspec).1 (hR _ hspec) (hreg _) hu hη k).1
  · exact (nullMeasurableSet_claims hb (hE _ hspec).1 (hR _ hspec) (hreg _) hu hη k).2

/-- **R95's amended SB3** (`Ly.SB3InductionGenRStatement`, the binder `hSB3` of Theorem 1.4's top) from SB2(1) in
GW1's ambient setting, Theorems 1.2–1.3, the small-gap fibre cover and the stage input (I5). -/
theorem sb3InductionGenRStatement_of_path (hSB2 : Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hPath : SB3StagePathRStatement.{u}) : Ly.SB3InductionGenRStatement.{u} :=
  Ly.sb3InductionGenRStatement_of_inputs_dyCover hSB2 h12 h13 h12₀ h13₀ hDy hDy₀
    (sb3StageInputsRStatement_of_path hPath)

end InteractingSLE.Theorem14.SB.LuM
