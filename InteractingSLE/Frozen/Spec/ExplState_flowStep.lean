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
import InteractingSLE.Frozen.Spec.ExplState
import InteractingSLE.Frozen.Spec.ExplState_heights
import InteractingSLE.Frozen.Spec.ExplState_IsAdmissibleSeed
import InteractingSLE.Frozen.Spec.ExplState_launch

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

open Classical in
/-- An ordinary-piece instruction (angle `θ`, own time `t`, instruction index `k`, driver `D`), for boundary data
`b`: from the root or an interior tip the piece is launched; at a threshold or connector point it is launched only
if its seed is admissible, and otherwise only the boundary continuation remains available (GW2a); for a GW2
schedule no switch is performed after a threshold (status *dead*). -/
def ExplState.flowStep (κ : ℝ) (b : ℝ → ℝ) (gw2 : Bool) (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) : ExplState :=
  let (pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL) := s
  match status with
  | .inl () => ExplState.launch s k D θ t  -- root
  | .inr (.inl ()) => ExplState.launch s k D θ t  -- tip
  | .inr (.inr (.inr (.inr (.inl ())))) => s  -- done
  | .inr (.inr (.inr (.inr (.inr ())))) => s  -- dead
  | _ =>
      if gw2 then
        (pieces, arcs, retained, launches, chart, .inr (.inr (.inr (.inr (.inr ())))), pt, angle, recR, recL)
      else if ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ then
        ExplState.launch s k D θ t
      else s

end InteractingSLE
