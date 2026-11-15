import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary

import InteractingSLE.Frozen.Spec.nullSigma

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The usual augmentation `𝓕⁺ₜ = ⋂_{s > t} σ(𝓕ₛ ∪ 𝒩)` of a filtration, `𝒩` the `P`-null sets
(Specification p. 4, "Filtrations have their usual augmentation"; §3.3, p. 73, "the usual
completion and right-continuous augmentation"). -/
def usualAugmentation {Ω : Type u} [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Filtration ℝ≥0 mΩ :=
  (𝓕 ⊔ Filtration.const ℝ≥0 (nullSigma P) (MeasurableSpace.generateFrom_le fun _ hs => hs.1)).rightCont

end InteractingSLE
