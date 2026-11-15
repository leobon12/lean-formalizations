-- FROZEN_ANCHOR_PREFIX_BEGIN
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
import InteractingSLE.Spec.Provider.IsCenteredCounterflowDriver_boundaryWalks_frontiers

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 1.4, frontiers** (Specification p. 5; proof interface GW1, BW3a–BW3, SB1–SB5, GW3–GW4, GW6). In the
setting of Theorem 1.4, for every realization `E` of the staged histories of `h` with angles in `[−π/2, π/2]`
(every launched piece almost surely a continuous curve with a continuous generating trace,
`StagedPiecesRegular`; ruling R51), almost surely: the actual right and left frontiers of `η'` are the angle
`−π/2` and `+π/2` finite boundary walks of
GW1 (which at a finite ordinary-flow continuation threshold follow the prescribed original-boundary connector and
continue at the next admissible seed): each walk lies in the completed range of `η'`, and that range has no point
strictly on the right of the right walk, resp. strictly on the left of the left walk. On the event that the
counterflow's intersection with the original boundary has empty relative interior, both walks are complete ordinary
extreme flow lines: their first ordinary pieces never reach a finite continuation threshold. -/
theorem IsCenteredCounterflowDriver.boundaryWalks_frontiers {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec)) :
    ∀ᵐ ω ∂P,
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅) ∧
      (interior (((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω)) = ∅ →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
          (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.IsCenteredCounterflowDriver_boundaryWalks_frontiers
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
