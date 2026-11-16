-- FROZEN_ANCHOR_PREFIX_BEGIN
-- Frozen anchor (theorem, spec_IsFlowLine_first_or_terminal_of_contact_of_critical_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
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
import InteractingSLE.Frozen.Spec.IsFirstContact
import InteractingSLE.Spec.Provider.IsFlowLine_first_or_terminal_of_contact_of_critical

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 1.5 (iii), critical angles, at every contact** (arXiv:1201.1496v2 p. 30: "If, in addition,
`θ₁ − θ₂ < πκ/(4 − κ)`, then `η₁` and `η₂` can bounce off of each other; otherwise the paths almost surely do not
subsequently intersect"; Specification Theorem 1.5 (iii), p. 5, and the critical exclusion after a crossing, p. 544,
there for interior contacts). With the setup of (iii) (`x₂ < x₁`, `θ₂ < θ₁ < θ₂ + π`) and `θ₁ − θ₂ ≥ πκ/(4 − κ)`:
almost surely, every common point `η₁ s = η₂ t` of the closed available paths (`s ≤ ζ₁`, `t ≤ ζ₂`; points of `ℍ` and
of `ℝ`, terminal values included) is either the first contact or terminal for both paths (`s = ζ₁` and `t = ζ₂`).
The second exception is needed: for suitable boundary data the paths cross and then end at the same real point
almost surely. -/
theorem IsFlowLine.first_or_terminal_of_contact_of_critical {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₂ < θ₁) (hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hcrit : Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t ∨ ((s : ℝ≥0∞) = ζ₁ ω ∧ (t : ℝ≥0∞) = ζ₂ ω) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.IsFlowLine_first_or_terminal_of_contact_of_critical
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
