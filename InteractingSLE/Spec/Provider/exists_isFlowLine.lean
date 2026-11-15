import InteractingSLE.Spec.Seal.Final

/-!
# Provider for a frozen anchor (sealed)

Anchor file: `InteractingSLE/Frozen/Spec/exists_isFlowLine.lean`.

The statement is the frozen anchor's with all arguments implicit and its hypotheses as auto-parameters (provider
convention); the proof is the closed provider
`InteractingSLE.Seal.Final.exists_isFlowLine` (PROVE-T12-ASSEMBLE5, seal round).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Spec.Provider

theorem exists_isFlowLine
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption) {x θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ :=
  by exact Seal.Final.exists_isFlowLine

end InteractingSLE.Spec.Provider
