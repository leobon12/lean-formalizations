/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkLaterSeedLaw

/-! # Exact split of the open later-exit input and its original consumers

The split is equivalent to the previous named input, rather than a stronger
assumption. None of its three mathematical clauses is claimed unconditionally.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkLaterSeed

open Exist.Staged Exist.StagedLaw WalkFirstSeed WalkCapBlock WalkSeedFinite
open PiecewiseConstantBoundaryData (jumpSet)

/-- The staged-law route to later finite exits, separating the active seed
condition from the still missing positive-lifetime endpoint geometry. -/
theorem ae_laterFiniteExitSeedData_of_stageSeeds {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hS : LaterStageSeedData κ b jumps θ right P h E)
    (hpos : ∀ᵐ ω ∂P, PositiveLaterExitSeedData κ b jumps θ right (fun j => E j ω)) :
    ∀ᵐ ω ∂P, LaterFiniteExitSeedData κ b jumps θ right (fun j => E j ω) := by
  filter_upwards [ae_noZeroLaterLaunchData_of_stageSeeds hκ hb hh hE hreg hS, hpos] with ω hn hp
  exact (laterFiniteExitSeedData_iff (fun j => E j ω)).2 ⟨hn, hp⟩

/-- The full original seed data follow from active-word seeds, positive later
exits and restart freshness. The first exit is supplied by Theorem 1.3. -/
theorem ae_walkSeedData_of_stageSeeds (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hS : LaterStageSeedData κ b jumps θ right P h E)
    (hpos : ∀ᵐ ω ∂P, PositiveLaterExitSeedData κ b jumps θ right (fun j => E j ω))
    (hfresh : ∀ᵐ ω ∂P, FreshRestartData κ b jumps θ right (fun j => E j ω)) :
    ∀ᵐ ω ∂P, WalkSeedData κ b jumps θ right (fun j => E j ω) := by
  filter_upwards [ae_first_seedBlocked h13 hκ hb hh hE (hreg 0),
    ae_laterFiniteExitSeedData_of_stageSeeds hκ hb hh hE hreg hS hpos, hfresh] with ω h0 hL hF
  exact seedData_of_finiteExits_freshRestarts (fun j => E j ω)
    (finiteExitSeedData_of_first_later _ h0 hL) hF

/-- The exact remaining off-sector input, split into zero-lifetime exclusion,
positive finite exits, and fresh original restart marks. This is an open
conditional helper, not a replacement for the original locality statement. -/
def OffAmbientSplitExitFreshStatement (θ : ℝ) (right : Bool) : Prop :=
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
        PositiveLaterExitSeedData κ b jumps θ right
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω) ∧
        FreshRestartData κ b jumps θ right
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω)

/-- Splitting the open input neither strengthens it nor removes any case. -/
theorem offAmbientLaterExitFreshStatement_iff_split {θ : ℝ} {right : Bool} :
    OffAmbientLaterExitFreshStatement.{u} θ right ↔ OffAmbientSplitExitFreshStatement.{u} θ right := by
  constructor
  · intro hL κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg hamb hJ
    filter_upwards [hL κ hκ hκ4 b jumps hb P h hh E hE hR hreg hamb hJ] with ω hω
    obtain ⟨hz, hp⟩ := (laterFiniteExitSeedData_iff _).1 hω.1
    exact ⟨hz, hp, hω.2⟩
  · intro hL κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg hamb hJ
    filter_upwards [hL κ hκ hκ4 b jumps hb P h hh E hE hR hreg hamb hJ] with ω hω
    exact ⟨(laterFiniteExitSeedData_iff _).2 ⟨hω.1, hω.2.1⟩, hω.2.2⟩

/-- The four unchanged original leaves from the equivalent split inputs. -/
theorem prefixInputs_of_splitExitFresh
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : OffAmbientSplitExitFreshStatement.{u} (-(Real.pi / 2)) true)
    (hL : OffAmbientSplitExitFreshStatement.{u} (Real.pi / 2) false) :
    WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false ∧
    WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false :=
  prefixInputs_of_laterExitFresh h12 h13
    (offAmbientLaterExitFreshStatement_iff_split.2 hR)
    (offAmbientLaterExitFreshStatement_iff_split.2 hL)

end InteractingSLE.Theorem14.WalkLaterSeed
