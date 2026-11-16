-- FROZEN_ANCHOR_PREFIX_BEGIN
-- Frozen anchor (theorem, spec_IsFlowLine_start_or_terminal_of_contact_of_critical_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
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
import InteractingSLE.Spec.Provider.IsFlowLine_start_or_terminal_of_contact_of_critical

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 1.5 (i), critical angles, at every contact** (arXiv:1201.1496v2 p. 30: "If, in addition,
`θ₂ − θ₁ < πκ/(4 − κ)`, then `η₁` and `η₂` can bounce off of each other; otherwise the paths almost surely do not
intersect (except possibly at their starting point)"; Specification Theorem 1.5 (i), p. 5, and Theorem 7.12D,
pp. 543–544, there for interior contacts). With the setup of (i) (`x₂ ≤ x₁`, `θ₁ < θ₂`) and `θ₂ − θ₁ ≥ πκ/(4 − κ)`:
almost surely, every common point `η₁ s = η₂ t` of the closed available paths (`s ≤ ζ₁`, `t ≤ ζ₂`; points of `ℍ` and
of `ℝ`, terminal values included) is either the common starting point (`x₁ = x₂` and `s = t = 0`) or terminal for both
paths (`s = ζ₁` and `t = ζ₂`). The second exception is needed: for suitable boundary data both flow lines end at the
same real point, which is not a starting point, almost surely. -/
theorem IsFlowLine.start_or_terminal_of_contact_of_critical {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hcrit : Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      (x₁ = x₂ ∧ s = 0 ∧ t = 0) ∨ ((s : ℝ≥0∞) = ζ₁ ω ∧ (t : ℝ≥0∞) = ζ₂ ω) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.IsFlowLine_start_or_terminal_of_contact_of_critical
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
