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

/-- `E_t(φ) = ∬ φ(y) G(f_t(y), f_t(z)) φ(z) dy dz`, `G(y, z) = log|y − z̄| − log|y − z|`
(Specification §3.3, p. 74–75): the variance of `(h̃⁰ ∘ f_t, φ)` for a zero-boundary GFF `h̃⁰`
on `ℍ` and `φ` supported in `ℍ \ K_t`. -/
def loewnerGreenEnergy (w : ℝ → ℝ) (t : ℝ) (φ : ℂ → ℝ) : ℝ :=
  ∫ y, ∫ z, φ y * QuantumZipper.greenH (QuantumZipper.fwdMap w t y)
    (QuantumZipper.fwdMap w t z) * φ z

end InteractingSLE
