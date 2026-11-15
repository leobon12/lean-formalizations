-- FROZEN_ANCHOR_PREFIX_BEGIN
-- Frozen anchor (theorem, spec_IsFlowLine_crosses_of_lt_of_contact_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
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
import InteractingSLE.Frozen.Spec.CrossesFromRightAt
import InteractingSLE.Spec.Provider.IsFlowLine_crosses_of_lt_of_contact

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 1.5 (iii)** (constant-angle interaction, crossing), arXiv:1201.1496v2 p. 30 ("upon intersecting, crosses
and then never crosses back"; "otherwise the paths almost surely do not subsequently intersect"), §7.2 p. 133 and
Proposition 7.12, p. 141, at the first intersection, which may lie on `∂ℍ` (Lemma 7.8, p. 137); Specification Theorem
7.12C (pp. 461, 542: "They have no common nontrivial open outgoing arc, and they cannot cross back") and the critical
exclusion after a crossing (pp. 543–544). With the setup of (i), `x₂ < x₁` and `θ₂ < θ₁ < θ₂ + π`: almost surely, if the
flow lines have an available contact `η₁ s = η₂ t` (`s < ζ₁`, `t < ζ₂`, the point interior or real), then their first
contact `(s₀, t₀)` is attained at one common point (possibly real); there the first curve crosses the second from right
to left and never crosses back (`CrossesFromRightAt`), and no open arc of either outgoing available path lies on the
other outgoing available path (in particular they do not merge). A contact at a terminal time triggers nothing by
itself. If moreover `θ₁ - θ₂ ≥ πκ/(4 - κ)`, almost surely every contact **in `ℍ`** of the closed available paths is the
first contact. Contacts at real points are not covered by this exclusion (the specification's interior convention,
p. 5; the paper's real-point claim is not proved). -/
theorem IsFlowLine.crosses_of_lt_of_contact {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₂ < θ₁) (hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    (∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω → (t : ℝ≥0∞) < ζ₂ ω → η₁ ω s = η₂ ω t →
        ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
          CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ ∧
          (∀ a a' : ℝ≥0, s₀ ≤ a → a < a' → (a' : ℝ≥0∞) ≤ ζ₁ ω →
            ¬ η₁ ω '' Set.Ioo a a' ⊆ η₂ ω '' {t : ℝ≥0 | t₀ ≤ t ∧ (t : ℝ≥0∞) < ζ₂ ω}) ∧
          ∀ c c' : ℝ≥0, t₀ ≤ c → c < c' → (c' : ℝ≥0∞) ≤ ζ₂ ω →
            ¬ η₂ ω '' Set.Ioo c c' ⊆ η₁ ω '' {s : ℝ≥0 | s₀ ≤ s ∧ (s : ℝ≥0∞) < ζ₁ ω}) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t → η₁ ω s ∈ QuantumZipper.H →
          IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.IsFlowLine_crosses_of_lt_of_contact
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
