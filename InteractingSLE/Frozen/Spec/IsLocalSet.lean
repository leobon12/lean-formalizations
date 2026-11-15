import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary

import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Frozen.Spec.hittingSigma
import InteractingSLE.Frozen.Spec.IsHarmonicDistOn
import InteractingSLE.Frozen.Spec.IsCondZeroBoundaryGFF

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Local set** (Specification §3.2, p. 49, after [SS13]). `A` (a random relatively closed
subset of `ℍ`, standing for `A ∪ ∂ℍ`) is a local set of the random distribution `h` on `ℍ` if
`(A, h)` is a random variable and a sample with the law of `(A, h)` can be produced by first
choosing a pair `(A, h₁)`, with `h₁` a distribution on `ℍ` whose restriction to `ℍ \ A` is
harmonic, and then sampling `h₂`, a zero-boundary GFF on `ℍ \ A` (extended by zero), and setting
`h = h₁ + h₂`. -/
def IsLocalSet {Ω : Type u} [MeasurableSpace Ω] (A : Ω → Set ℂ)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (P : Measure Ω) : Prop :=
  letI : MeasurableSpace (Set ℂ) := hittingSigma
  AEMeasurable (fun ω => (A ω, h ω)) P ∧
    (∀ᵐ ω ∂P, A ω ⊆ QuantumZipper.H ∧ IsOpen (QuantumZipper.H \ A ω)) ∧
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (A' : Ω' → Set ℂ) (h₁ h₂ : Ω' → LQGMetric.DistOn upperHalfPlaneOpens),
      Measurable A' ∧ Measurable h₁ ∧ Measurable h₂ ∧
      (∀ ω', A' ω' ⊆ QuantumZipper.H ∧ IsOpen (QuantumZipper.H \ A' ω')) ∧
      (∀ᵐ ω' ∂P', IsHarmonicDistOn (h₁ ω') (QuantumZipper.H \ A' ω')) ∧
      IsCondZeroBoundaryGFF P' (MeasurableSpace.comap A' hittingSigma ⊔
          MeasurableSpace.comap h₁ inferInstance)
        (fun ω' => QuantumZipper.H \ A' ω') h₂ ∧
      P'.map (fun ω' => (A' ω', h₁ ω' + h₂ ω')) = P.map (fun ω => (A ω, h ω))

end InteractingSLE
