/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkRecordSeedFinite

/-! # Walk-side leaves after discharging positive finite exits

The remaining named input contains only later nonzero lifetimes and restart
freshness. The old positive finite-exit clause is supplied by the staged law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkRecordSeed

open Exist.Staged Exist.StagedLaw WalkSeedFinite WalkCapBlock WalkLaterSeed
open PiecewiseConstantBoundaryData (jumpSet)

/-- The exact remaining off-sector mathematics after proving every positive
finite exit. These two clauses remain unproved; this is a conditional helper. -/
def OffAmbientNoZeroFreshStatement (θ : ℝ) (right : Bool) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), IsRegularDriver (E spec k ω)) →
      ¬ AmbientSideBound κ b jumps θ right → (jumpSet b jumps).Nonempty →
      ∀ᵐ ω ∂P,
        NoZeroLaterLaunchData κ b jumps θ right
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω) ∧
        FreshRestartData κ b jumps θ right
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω)

/-- The remaining pair is equivalent to the previous triple because its
positive finite-exit clause follows from the actual walk's staged history. -/
theorem offAmbientSplitExitFreshStatement_iff_noZeroFresh {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {right : Bool} :
    OffAmbientSplitExitFreshStatement.{u} θ right ↔ OffAmbientNoZeroFreshStatement.{u} θ right := by
  constructor
  · intro hS κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg hamb hJ
    filter_upwards [hS κ hκ hκ4 b jumps hb P h hh E hE hR hreg hamb hJ] with ω hω
    exact ⟨hω.1, hω.2.2⟩
  · intro hN κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg hamb hJ
    have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
    have hpos := ae_positiveLaterExitSeedData hκ hb hh (hE _ hw)
      (fun j ω => hreg (boundaryWalkSpec b jumps θ right) j ω)
    filter_upwards [hN κ hκ hκ4 b jumps hb P h hh E hE hR hreg hamb hJ, hpos] with ω hω hp
    exact ⟨hω.1, hp, hω.2⟩

/-- All four exact original leaves after removing the now proved positive
finite exits from the remaining mathematical assumptions. -/
theorem prefixInputs_of_noZeroFresh
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : OffAmbientNoZeroFreshStatement.{u} (-(Real.pi / 2)) true)
    (hL : OffAmbientNoZeroFreshStatement.{u} (Real.pi / 2) false) :
    WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false ∧
    WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false :=
  prefixInputs_of_splitExitFresh h12 h13
    ((offAmbientSplitExitFreshStatement_iff_noZeroFresh
      ⟨le_rfl, by linarith only [Real.pi_pos]⟩).2 hR)
    ((offAmbientSplitExitFreshStatement_iff_noZeroFresh
      ⟨by linarith only [Real.pi_pos], le_rfl⟩).2 hL)

end InteractingSLE.Theorem14.WalkRecordSeed
