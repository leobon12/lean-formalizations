import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary


set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The upper half-plane `ℍ = {z : 0 < Im z}` as an open subset of `ℂ`
(`QuantumZipper.H`), the domain of the fields of Theorems 1.1–1.2. -/
def upperHalfPlaneOpens : Opens ℂ := ⟨QuantumZipper.H, QuantumZipper.isOpen_H⟩

end InteractingSLE
