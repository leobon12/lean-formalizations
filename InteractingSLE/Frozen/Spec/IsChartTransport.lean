import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Frozen.Spec.Chart

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- `h'` is the field `σ h + a` written in the chart `c = (fwd, inv, lift)` by the coordinate rule (1.4) with
coefficient `k` (`k = χ(κ)` for a flow field, `k = χ(κ′) = −χ` for a counterflow parameter field, FD11.2):
`h' = (σ h + a) ∘ inv + k · (lift ∘ inv)` on `ℍ` (since `−Im L_inv = lift ∘ inv`). As distributions,
`⟨h', φ'⟩ = σ ⟨h, φ⟩ + a ∫ φ' + k ∫ (lift ∘ inv) φ'` whenever `φ` is the transported test function,
`φ = (φ' ∘ fwd) · |fwd′|²` on `U = inv '' ℍ` with support in `U` (change of variables `w = fwd z`). For a
conformal chart every `φ'` has exactly one such `φ`, so the relation determines `h'`. -/
def IsChartTransport (c : Chart) (σ a k : ℝ) (h h' : LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  ∀ φ φ' : LQGMetric.TestOn upperHalfPlaneOpens,
    tsupport φ ⊆ c.2.1 '' QuantumZipper.H →
    (∀ z ∈ c.2.1 '' QuantumZipper.H, φ z = φ' (c.1 z) * ‖deriv c.1 z‖ ^ 2) →
    h' φ' = σ * h φ + a * (∫ w, φ' w) + k * ∫ w, c.2.2 (c.2.1 w) * φ' w

/-! ## G2. Flow lines and the centred counterflow, through the coupling of Theorem 1.1 -/

end InteractingSLE
