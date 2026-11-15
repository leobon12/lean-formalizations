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

/-- The coupling mean `𝔥_t(z) = 𝔥⁰_t(f_t(z)) − χ arg f_t′(z)` of Theorem 1.1 (p. 9), for a
driving function `w`, a time `t`, and `u = 𝔥⁰_t` the bounded harmonic extension of the time-`t`
boundary data. `f_t = QuantumZipper.fwdMap w t` is the centred Loewner map and
`arg f_t′ = Im (QuantumZipper.logDerivFwd w t)`, `logDerivFwd w t z = −∫₀ᵗ 2/f_s(z)² ds`, the
continuous branch of `log f_t′` that vanishes at `t = 0`; `χ = QuantumZipper.chiC κ`. -/
def couplingMean (κ : ℝ) (w : ℝ → ℝ) (t : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  u (QuantumZipper.fwdMap w t z) - QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd w t z).im

end InteractingSLE
