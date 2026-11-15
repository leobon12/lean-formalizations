/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkFirstSeedNoMarks

/-!
# Walk-side inputs after proving the first exit and the case without marks

The remaining named hypothesis is restricted to later finite actual launches
for off-sector boundary words having at least one genuine jump, together with
freshness of admissible original restart marks. The first exit and words
without original marks require no additional mathematical input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkFirstSeed

open Exist.Staged Exist.StagedLaw WalkCapBlock WalkSeedFinite
open PiecewiseConstantBoundaryData (jumpSet)

/-- The exact remaining off-sector input after the first-launch theorem:
later finite exits and fresh admissible restarts, only for nonempty jump sets.
This is a conditional helper and does not replace an original statement. -/
def OffAmbientLaterExitFreshStatement (θ : ℝ) (right : Bool) : Prop :=
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
        LaterFiniteExitSeedData κ b jumps θ right
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω) ∧
        FreshRestartData κ b jumps θ right
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω)

/-- The full old finite-exit input follows after proving the first exit and
separately settling words without original jump marks. -/
theorem offAmbientExitFreshStatement_of_later (h13 : Exist.Theorem13Statement.{u})
    {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {right : Bool}
    (hL : OffAmbientLaterExitFreshStatement.{u} θ right) : OffAmbientExitFreshStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg hamb
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  have h0 := ae_first_seedBlocked h13 hκ hb hh (hE _ hw)
    (fun ω => hreg (boundaryWalkSpec b jumps θ right) 0 ω)
  by_cases hJ : (jumpSet b jumps).Nonempty
  · filter_upwards [h0, hL κ hκ hκ4 b jumps hb P h hh E hE hR hreg hamb hJ] with ω hfirst hω
    exact ⟨finiteExitSeedData_of_first_later _ hfirst hω.1, hω.2⟩
  · have he : jumpSet b jumps = ∅ := Finset.not_nonempty_iff_eq_empty.1 hJ
    filter_upwards [h0] with ω hfirst
    exact ⟨finiteExitSeedData_of_first_later _ hfirst (laterFiniteExitSeedData_of_no_marks _ he),
      freshRestartData_of_no_marks _ he⟩

/-- All four exact original packet leaves, with index zero and the words
without genuine jumps removed from the remaining mathematical inputs. -/
theorem prefixInputs_of_laterExitFresh
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : OffAmbientLaterExitFreshStatement.{u} (-(Real.pi / 2)) true)
    (hL : OffAmbientLaterExitFreshStatement.{u} (Real.pi / 2) false) :
    WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false ∧
    WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false :=
  prefixInputs_of_exitFresh h12 h13
    (offAmbientExitFreshStatement_of_later h13 ⟨le_rfl, by linarith only [Real.pi_pos]⟩ hR)
    (offAmbientExitFreshStatement_of_later h13 ⟨by linarith only [Real.pi_pos], le_rfl⟩ hL)

end InteractingSLE.Theorem14.WalkFirstSeed
