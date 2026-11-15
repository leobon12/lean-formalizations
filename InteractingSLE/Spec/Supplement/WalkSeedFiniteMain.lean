/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSeedFiniteCount

/-!
# Walk-side inputs from finite exits and fresh restarts

Packet PROVE-T14-WALKSIDE2. The proved ambient sector is retained. Outside it,
the remaining endpoint and no-revisit assertions are named explicitly below.
The final seed and all infinite-lifetime cases follow from proved deterministic
lemmas. These are conditional helpers; the original packet statements and the
landed providers remain unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkSeedFinite

open Exist.Staged Exist.StagedLaw WalkCapBlock

/-- The still-unproved off-sector endpoint and no-revisit input. The clauses
concern finite actual exits and original restart points, with no final-state
assertion and no condition on artificial caps or unused drivers. -/
def OffAmbientExitFreshStatement (θ : ℝ) (right : Bool) : Prop :=
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
      ¬ AmbientSideBound κ b jumps θ right →
      ∀ᵐ ω ∂P,
        FiniteExitSeedData κ b jumps θ right
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω) ∧
        FreshRestartData κ b jumps θ right
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω)

/-- The remaining seed input follows from finite exits and fresh restart
points. The final-state assertion is proved by finite counting. -/
theorem offAmbientSeedStatement_of_exitFresh {θ : ℝ} {right : Bool}
    (hEF : OffAmbientExitFreshStatement.{u} θ right) : OffAmbientSeedStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg hamb
  filter_upwards [hEF κ hκ hκ4 b jumps hb P h hh E hE hR hreg hamb] with ω hω
  exact seedData_of_finiteExits_freshRestarts
    (fun j => E (boundaryWalkSpec b jumps θ right) j ω) hω.1 hω.2

/-- An adapter to the landed non-launch interface, keeping all of its
original quantifiers. No off-sector exit classification is asserted here. -/
theorem nonFlowCapNoLaunchStatement_of_exitFresh {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {right : Bool}
    (hEF : OffAmbientExitFreshStatement.{u} θ right) :
    WalkSideResume.NonFlowCapNoLaunchStatement.{u} θ right :=
  nonFlowCapNoLaunchStatement_of_offAmbientSeeds hθ
    (offAmbientSeedStatement_of_exitFresh hEF)

/-- All four original packet leaves from Theorems 1.2–1.3 and the two named
off-sector exit/freshness hypotheses. Neither source theorem is replaced. -/
theorem prefixInputs_of_exitFresh
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : OffAmbientExitFreshStatement.{u} (-(Real.pi / 2)) true)
    (hL : OffAmbientExitFreshStatement.{u} (Real.pi / 2) false) :
    WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false ∧
    WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false :=
  prefixInputs_of_offAmbientSeeds h12 h13
    (offAmbientSeedStatement_of_exitFresh hR) (offAmbientSeedStatement_of_exitFresh hL)

end InteractingSLE.Theorem14.WalkSeedFinite
