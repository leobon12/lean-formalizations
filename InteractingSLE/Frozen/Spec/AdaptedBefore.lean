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

/-- A real process `X` that is only defined before the random time `ζ` is adapted to `𝓕`
(Definition 2.1, p. 20, "continuous adapted processes", for processes that live on `[0, ζ)`):
for every `t` and Borel `A`, the event `{t < ζ, X_t ∈ A}` belongs to `𝓕_t`. This is adaptedness
of the process killed at `ζ` (with a cemetery state); taking `A = univ` shows `{t < ζ} ∈ 𝓕_t`. -/
def AdaptedBefore {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (t : ℝ≥0) (A : Set ℝ), MeasurableSet A →
    MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A}

end InteractingSLE
