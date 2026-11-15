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
import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- `h` is a GFF on `ℍ` whose mean is the bounded harmonic extension of `g` (continuous off `S`):
`h` is measurable and `h - 𝔥_g` is a zero-boundary GFF on `ℍ` (Specification p. 2, (1.3); item 2 of
`IsOptionalHullCoupling`, factored out). -/
def IsGFFWithBoundaryData {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (g : ℝ → ℝ) (S : Set ℝ) : Prop :=
  Measurable h ∧ ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension g S u₀ →
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P

end InteractingSLE
