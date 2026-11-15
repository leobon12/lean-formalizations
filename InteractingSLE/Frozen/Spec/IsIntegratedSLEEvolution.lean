import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary

import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal
import InteractingSLE.Frozen.Spec.AdaptedBefore
import InteractingSLE.Frozen.Spec.IsIntegratedSLEPath

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- An integrated `SLE_a(ρ)` driving evolution for the force word with positions `(xL; xR)` and weights
`(ρL; ρR)` on the filtered probability space `(Ω, 𝓕, P)`, with lifetime `ζ` (Specification p. 3; Definition 2.1,
p. 20): a Brownian motion `B` in the filtration, coordinates `W`, `V^{i,q}` that are adapted on `[0, ζ)`, and almost
surely the pathwise conditions `IsIntegratedSLEPath`. The lifetime `ζ` is the continuation
threshold `T_*`. -/
def IsIntegratedSLEEvolution (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  -- brownian
  IsFilteredBrownianReal 𝓕 B P ∧
  -- adapted_W
  AdaptedBefore 𝓕 ζ W ∧
  -- adapted_VL
  (∀ i, AdaptedBefore 𝓕 ζ (VL i)) ∧
  -- adapted_VR
  (∀ i, AdaptedBefore 𝓕 ζ (VR i)) ∧
  -- ae_path
  ∀ᵐ ω ∂P, IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)

end InteractingSLE
