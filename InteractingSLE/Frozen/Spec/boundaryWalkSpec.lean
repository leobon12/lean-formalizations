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
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_jumpSet
import InteractingSLE.Frozen.Spec.Instr
import InteractingSLE.Frozen.Spec.ExplSpec

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The finite boundary walk of GW1 (p. 618) at angle `θ` (`−π/2`: the right walk `R`; `π/2`: the left walk `L`,
continuing to the right resp. left), for boundary data `b` (locally constant off `jumps`): run the ordinary
angle-`θ` flow through its available lifetime (*flow* `.inl (θ, ⊤)`); at a finite threshold follow the original
boundary to the next admissible original mark and repeat (*cont* `.inr (.inl right)`). Each restart uses a new
original jump, so `#jumps + 1` rounds suffice; later instructions do nothing once the target is reached. -/
def boundaryWalkSpec (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) : ExplSpec :=
  ⟨0, false, (List.replicate ((PiecewiseConstantBoundaryData.jumpSet b jumps).card + 1)
    [(Sum.inl (θ, ⊤) : Instr), Sum.inr (Sum.inl right)]).flatten⟩

end InteractingSLE
