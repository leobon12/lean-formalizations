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

/-- The σ-algebra generated up to time `t` by the driving process `(W, V^{·,L}, V^{·,R})` killed
at its lifetime `ζ` (the process is defined only before `ζ`; ARCH-1, D2 and D5): it is generated
by the events `{r < ζ, (W_r, V^L_r, V^R_r) ∈ A}`, `r ≤ t`, `A` Borel. -/
@[instance_reducible]
def killedDrivingSigma {Ω : Type u} {nL nR : ℕ} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom
    {E | ∃ r ≤ t, ∃ A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)), MeasurableSet A ∧
      E = {ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A}}

end InteractingSLE
