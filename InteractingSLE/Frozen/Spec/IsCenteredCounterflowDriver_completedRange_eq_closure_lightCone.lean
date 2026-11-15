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
import InteractingSLE.Frozen.Spec.Instr
import InteractingSLE.Frozen.Spec.ExplSpec
import InteractingSLE.Frozen.Spec.ExplState
import InteractingSLE.Frozen.Spec.ExplState_physSet
import InteractingSLE.Frozen.Spec.IsStagedHistory
import InteractingSLE.Frozen.Spec.boundaryLightConeFamily
import InteractingSLE.Frozen.Spec.IsBoundaryContinuedProgram
import InteractingSLE.Frozen.Spec.StagedPiecesRegular
import InteractingSLE.Spec.Provider.IsCenteredCounterflowDriver_completedRange_eq_closure_lightCone

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 1.4, light cone** (Specification pp. 4–5; proof interface GW0, GW2, GW2a, SB1–SB5, GW6). Let
`0 < κ < 4`, let `h` be a GFF on `ℍ` with a finite piecewise-constant boundary word `b` (locally constant off
`jumps`), and let `η' = CF_d(h)` run from `∞` to `0` in the centred frame, with its infinity-source derivative lift
FD12.1–FD12.2 (driver `W'` in the chart `R`, lifetime `ζ'`). Suppose that `η'` almost surely never hits its
continuation threshold. Fix a countable dense `Θ ⊂ (−π/2, π/2)`. There is a deterministic countable dense schedule
set `Q ⊂ (0, ∞)` such that, for every realization `E` of the staged histories of `h` with angles in `[−π/2, π/2]`
(every ordinary piece the flow line of its conditional field)
(every launched piece almost surely a continuous curve with a continuous generating trace,
`StagedPiecesRegular`; ruling R51):
* almost surely, the entire completed range of `η'` is the closure of the GW2 family together with the initial
  point `0` — available finite `Θ`-histories with times in `Q`, each retained through its actual lifetime, and, when
  the lower extreme seed is inadmissible, the forced original-boundary connectors `[0, v]` and the schedules from
  the countable roots `v`;
* for every fixed countable collection of prescribed finite histories with angles in `[−π/2, π/2]` and the GW2a
  boundary-continuation rule (in particular the available extreme-angle histories and the finite boundary
  continuations), adding them gives almost surely the same closed range. -/
theorem IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (Θ : Set ℝ) (hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hΘc : Θ.Countable)
    (hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ) :
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        (∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
            counterflowCompletedRange (fun t => W' t ω)) ∧
        ∀ 𝒞 : Set (List Instr), 𝒞.Countable → (∀ p ∈ 𝒞, IsBoundaryContinuedProgram p) →
          ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪
              (⋃ p ∈ 𝒞, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω)) ∪
              {0}) =
            counterflowCompletedRange (fun t => W' t ω) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.IsCenteredCounterflowDriver_completedRange_eq_closure_lightCone
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
