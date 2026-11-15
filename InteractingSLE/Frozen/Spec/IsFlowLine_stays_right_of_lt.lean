-- FROZEN_ANCHOR_PREFIX_BEGIN
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
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Frozen.Spec.IsFlowLine
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions
import InteractingSLE.Frozen.Spec.IsInteriorAvailableContact
import InteractingSLE.Spec.Provider.IsFlowLine_stays_right_of_lt

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 1.5 (i)** (constant-angle interaction, ordered angles), Specification p. 5; proof
interface W5 (p. 533) and Theorem 7.12D (p. 543). Let `0 < κ < 4`, let `h` be a GFF on `ℍ` with
finite piecewise-constant boundary data `b` (locally constant off `jumps`), let `x₂ ≤ x₁` and
`θ₁ < θ₂`, and let `η₁ = η^{x₁}_{θ₁}`, `η₂ = η^{x₂}_{θ₂}` be the angle-`θᵢ` flow lines of `h` from
`xᵢ`, with available lifetimes `ζᵢ`. Then almost surely `η₁` stays to the right of `η₂`: every pair
of finite prefixes strictly before the lifetimes has ordered proper completions with `η₂` on the
left (W0). If moreover `θ₂ - θ₁ ≥ πκ/(4 - κ)`, almost surely they have no interior available
contact (a common starting point is real, hence not interior). -/
theorem IsFlowLine.stays_right_of_lt {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    (∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        ¬ IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.IsFlowLine_stays_right_of_lt
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
