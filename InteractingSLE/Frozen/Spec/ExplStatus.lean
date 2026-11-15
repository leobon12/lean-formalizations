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

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- Where a staged history currently stands, as an element of `Unit ⊕ Unit ⊕ Option Bool ⊕ (Bool × Bool) ⊕ Unit ⊕
Unit`:
* `.inl ()` (*root*): at the root; nothing has been run yet;
* `.inr (.inl ())` (*tip*): at the interior tip of an ordinary piece stopped at an available own time;
* `.inr (.inr (.inl side))` (*thr*): at the finite continuation threshold of the last ordinary piece, on the
  original boundary: `side = some true` a new right record, `some false` a new left record, `none` an immediately
  inadmissible seed (zero lifetime);
* `.inr (.inr (.inr (.inl (right, atMark))))` (*onArc*): on a recorded original-boundary connector moving right
  (`right = true`) or left; `atMark` when at its restart mark;
* `.inr (.inr (.inr (.inr (.inl ()))))` (*done*): the history has reached the target `∞`;
* `.inr (.inr (.inr (.inr (.inr ()))))` (*dead*): the prescribed history is no longer available. -/
@[reducible]
def ExplStatus : Type := Unit ⊕ Unit ⊕ Option Bool ⊕ (Bool × Bool) ⊕ Unit ⊕ Unit

end InteractingSLE
