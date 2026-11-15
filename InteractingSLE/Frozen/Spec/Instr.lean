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

/-- One instruction of a prescribed finite staged history (Lemma GW2a, p. 623; the walks of Lemma GW1, p. 618; the
schedules of Lemma GW2, p. 621), as an element of `(ℝ × ℝ≥0∞) ⊕ Bool ⊕ (ℝ × Bool)`:
* `.inl (θ, t)` (*flow*): run the next ordinary piece at angle `θ` for own capacity time `t` (`t = ⊤`: through its
  available lifetime). A switch is performed only at a strictly available own stop.
* `.inr (.inl pref)` (*cont*): boundary continuation (GW2a rule): from a finite threshold, or from a point of a
  recorded connector, move outward on the untouched original boundary to the first later original jump whose
  outward height is admissible for the current angle. `pref` (`true`: right) is the specified direction when an
  initial angle has two immediately bad sides.
* `.inr (.inr (v, pref))` (*contTo*): the same boundary continuation, stopped at the chosen point `v` if `v` lies
  strictly inside the forced arc (an angle change at a chosen point of a recorded connector, GW2a). -/
@[reducible]
def Instr : Type := (ℝ × ℝ≥0∞) ⊕ Bool ⊕ (ℝ × Bool)

end InteractingSLE
