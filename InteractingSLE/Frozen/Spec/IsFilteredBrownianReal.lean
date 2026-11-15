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

/-- `B` is a standard real Brownian motion with respect to the filtration `𝓕` ("a Brownian
motion `B` in their joint filtration", Specification p. 3 and Definition 2.1, p. 20): `B` is a
Brownian motion (Mathlib's `IsBrownianReal`: Brownian finite-dimensional laws and almost surely
continuous paths), it is `𝓕`-adapted, and each increment `B_t - B_s`, `s ≤ t`, is independent of
`𝓕_s`. -/
def IsFilteredBrownianReal {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsBrownianReal B P ∧ Adapted 𝓕 B ∧
    ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (𝓕 s) P

end InteractingSLE
