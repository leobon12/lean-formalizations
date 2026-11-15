/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkFreshRecordLaw

/-! # Walk-side inputs after proving restart freshness

The only remaining named seed input excludes zero lifetimes at actual later
launches. No freshness or positive finite-exit premise remains.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkFreshRecord

open Exist.Staged Exist.StagedLaw WalkCapBlock WalkLaterSeed WalkRecordSeed
open PiecewiseConstantBoundaryData (jumpSet)

/-- The exact remaining off-sector hypothesis: later actual launches have
nonzero lifetimes. This is an open conditional helper, not a source theorem. -/
def OffAmbientNoZeroStatement (θ : ℝ) (right : Bool) : Prop :=
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
      ∀ᵐ ω ∂P, NoZeroLaterLaunchData κ b jumps θ right
        (fun j => E (boundaryWalkSpec b jumps θ right) j ω)

/-- The former two-clause input is equivalent to the single nonzero-lifetime
clause, because restart freshness is proved from the actual staged law. -/
theorem offAmbientNoZeroFreshStatement_iff_noZero {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {right : Bool} :
    OffAmbientNoZeroFreshStatement.{u} θ right ↔ OffAmbientNoZeroStatement.{u} θ right := by
  constructor
  · intro hF κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg hamb hJ
    exact (hF κ hκ hκ4 b jumps hb P h hh E hE hR hreg hamb hJ).mono fun _ hω => hω.1
  · intro hN κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg hamb hJ
    have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
    have hfr := ae_freshRestartData hκ hb hh (hE _ hw)
      (fun j ω => hreg (boundaryWalkSpec b jumps θ right) j ω)
    filter_upwards [hN κ hκ hκ4 b jumps hb P h hh E hE hR hreg hamb hJ, hfr] with ω hω hf
    exact ⟨hω, hf⟩

/-- All four unchanged original packet leaves now require only the two
endpoint instances of the later nonzero-lifetime input. -/
theorem prefixInputs_of_noZero
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : OffAmbientNoZeroStatement.{u} (-(Real.pi / 2)) true)
    (hL : OffAmbientNoZeroStatement.{u} (Real.pi / 2) false) :
    WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false ∧
    WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false :=
  prefixInputs_of_noZeroFresh h12 h13
    ((offAmbientNoZeroFreshStatement_iff_noZero ⟨le_rfl, by linarith only [Real.pi_pos]⟩).2 hR)
    ((offAmbientNoZeroFreshStatement_iff_noZero ⟨by linarith only [Real.pi_pos], le_rfl⟩).2 hL)

end InteractingSLE.Theorem14.WalkFreshRecord
