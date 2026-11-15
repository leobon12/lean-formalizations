-- FROZEN_ANCHOR_PREFIX_BEGIN
-- Frozen anchor (theorem, spec_IsCenteredCounterflowDriver_boundaryWalks_outerBoundaries_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver
import InteractingSLE.Frozen.Spec.counterflowCompletedRange
import InteractingSLE.Frozen.Spec.ExplSpec
import InteractingSLE.Frozen.Spec.ExplState
import InteractingSLE.Frozen.Spec.ExplState_physSet
import InteractingSLE.Frozen.Spec.IsStagedHistory
import InteractingSLE.Frozen.Spec.IsBoundaryContinuedProgram
import InteractingSLE.Frozen.Spec.StagedPiecesRegular
import InteractingSLE.Frozen.Spec.boundaryWalkSpec
import InteractingSLE.Frozen.Spec.rightSideOf
import InteractingSLE.Frozen.Spec.leftSideOf
import InteractingSLE.Frozen.Spec.Chart_id
import InteractingSLE.Frozen.Spec.Chart_tipSet
import InteractingSLE.Spec.Provider.IsCenteredCounterflowDriver_boundaryWalks_outerBoundaries

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 1.4, the walks are the boundaries of the counterflow line** (arXiv:1201.1496v2 p. 22: "ηL and ηR are
the left and right boundaries of η′" when η′ is nowhere boundary filling; Specification pp. 4–5). In the setting of
`IsCenteredCounterflowDriver.boundaryWalks_frontiers`, almost surely, if the completed range `K` of `η′` meets `ℝ` in a
set with empty interior: both walks are single complete flow lines (`R = {0} ∪` the trace of the right walk's first
piece, and likewise `L`); `R` is the part of `K` on the frontier of the region `rightSideOf K` strictly to the right of
`K`, and also the closure of that frontier's points in `ℍ`; likewise `L` on the left; and `R ∪ L` is the outer
boundary of `K` in both senses. All sets are subsets of `ℂ`; the point at infinity is left out on both sides.
Requested by the external audit of 2026-11-15 (ruling R122; audit AUD-AF-T14). -/
theorem IsCenteredCounterflowDriver.boundaryWalks_outerBoundaries :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
      ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
      ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
        (∀ᵐ ω ∂P, ζ' ω = ⊤) →
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        ∀ᵐ ω ∂P,
          let K := counterflowCompletedRange (fun t => W' t ω)
          let R := ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
          let L := ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
          interior (((↑) : ℝ → ℂ) ⁻¹' K) = ∅ →
            ((E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
              (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤) ∧
            (R = {0} ∪ Chart.id.tipSet (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).1 ⊤ ∧
              L = {0} ∪ Chart.id.tipSet (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).1 ⊤) ∧
            (R = frontier (rightSideOf K) ∩ K ∧ L = frontier (leftSideOf K) ∩ K) ∧
            (R = closure (frontier (rightSideOf K) ∩ QuantumZipper.H) ∧
              L = closure (frontier (leftSideOf K) ∩ QuantumZipper.H)) ∧
            (R ∪ L = frontier (rightSideOf K ∪ leftSideOf K) ∩ K ∧
              R ∪ L = closure (frontier (rightSideOf K ∪ leftSideOf K) ∩ QuantumZipper.H)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.IsCenteredCounterflowDriver_boundaryWalks_outerBoundaries
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
