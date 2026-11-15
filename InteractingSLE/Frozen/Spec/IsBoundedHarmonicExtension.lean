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

/-- `u` is a bounded harmonic extension in `ℍ` of the boundary data `g` off the exceptional set
`S` (Specification p. 2: "their harmonic extension means the bounded harmonic extension in that
specified chart"; Theorem 1.1, p. 9): `u` is harmonic on `ℍ`, bounded on `ℍ`, and tends to
`g x` at every real boundary point `x ∉ S`. Only the values of `u` on `ℍ` are constrained. -/
def IsBoundedHarmonicExtension (g : ℝ → ℝ) (S : Set ℝ) (u : ℂ → ℝ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u QuantumZipper.H ∧
    (∃ C : ℝ, ∀ z ∈ QuantumZipper.H, |u z| ≤ C) ∧
    ∀ x : ℝ, x ∉ S → Tendsto u (𝓝[QuantumZipper.H] (x : ℂ)) (𝓝 (g x))

end InteractingSLE
