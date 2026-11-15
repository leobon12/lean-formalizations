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
import InteractingSLE.Frozen.Spec.sleLambda

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

open Classical in
/-- `bC` (locally constant off the finite set `jumpsC`) is the conditional flow-oriented boundary word (GW3.1) of
Lemma GW3 (p. 636) of a component between the walks, read in a component chart with inverse `inv`, for the flow
field whose original boundary data is `b`: at a real point `x ∉ jumpsC` whose boundary point `p = lim inv` lies on an
ordinary extremal piece (`ordR` for `x > 0`, the right incoming side; `ordL` for `x < 0`, the left incoming side)
the value is `−Λ` (right) or `+Λ` (left), `Λ = λ − (π/2)χ`; otherwise `p` lies on an original-real connector and the
value is the actual original boundary value `b(p)` ("The real values are the actual original boundary values"; an
original-real contact of an ordinary piece is treated on its flow-incident collar, GW3 proof). The marks of the
word (original height jumps, flow/connector junctions) are among the points of `jumpsC`. -/
def IsComponentBoundaryData (κ : ℝ) (b : ℝ → ℝ) (ordR ordL : Set ℂ) (inv : ℂ → ℂ) (bC : ℝ → ℝ)
    (jumpsC : Finset ℝ) : Prop :=
  ∀ x : ℝ, x ∉ jumpsC → ∀ p : ℂ, Tendsto inv (𝓝[QuantumZipper.H] (x : ℂ)) (𝓝 p) →
    (0 < x → bC x =
      if p ∈ ordR then -(sleLambda κ - Real.pi / 2 * QuantumZipper.chiC κ) else b p.re) ∧
    (x < 0 → bC x =
      if p ∈ ordL then sleLambda κ - Real.pi / 2 * QuantumZipper.chiC κ else b p.re)

end InteractingSLE
