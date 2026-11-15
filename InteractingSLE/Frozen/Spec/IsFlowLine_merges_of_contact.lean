-- FROZEN_ANCHOR_PREFIX_BEGIN
-- Frozen anchor (theorem, spec_IsFlowLine_merges_of_contact_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
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
import InteractingSLE.Frozen.Spec.AgreeAsCurvesAfter
import InteractingSLE.Spec.Provider.IsFlowLine_merges_of_contact

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 1.5 (ii)** (constant-angle interaction, equal angles), arXiv:1201.1496v2 p. 30 ("upon intersecting, the
two curves merge and never separate") and Proposition 7.12, p. 141, at the first intersection, which may lie on `∂ℍ`
(Lemma 7.8, p. 137); Specification Corollary 7.12E (p. 460) and Theorem 7.12C (p. 542). With the setup of (i) and a
common angle `θ`: almost surely, at every contact `η₁ s = η₂ t` of the closed available paths (`s ≤ ζ₁`, `t ≤ ζ₂`; the
contact point interior or real, a common seed included) the two flow lines agree as ordered unparametrized curves after
it until the shorter available portion ends. At a terminal contact (`s = ζ₁` or `t = ζ₂`) the shorter portion is the
contact point itself: no post-contact arc is asserted there. -/
theorem IsFlowLine.merges_of_contact {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ : ℝ} (hx : x₂ ≤ x₁)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      AgreeAsCurvesAfter (η₁ ω) (ζ₁ ω) s (η₂ ω) (ζ₂ ω) t :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.IsFlowLine_merges_of_contact
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
