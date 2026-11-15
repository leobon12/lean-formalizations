import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- `h' = h(· + x) + c` (coordinate change (1.4) for the chart `z ↦ z - x`, plus the constant
`c`): `⟨h', φ'⟩ = ⟨h, φ⟩ + c ∫ φ'` whenever `φ'(z) = φ(z + x)`. -/
def IsTranslateAddConst (x c : ℝ) (h h' : LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  ∀ φ φ' : LQGMetric.TestOn upperHalfPlaneOpens, (∀ z : ℂ, φ' z = φ (z + x)) →
    h' φ' = h φ + c * ∫ z, φ' z

end InteractingSLE
