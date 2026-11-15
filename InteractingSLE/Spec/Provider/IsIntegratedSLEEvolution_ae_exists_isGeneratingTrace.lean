import InteractingSLE.Spec.Seal.Final

/-!
# Provider for a frozen anchor (sealed)

Anchor file: `InteractingSLE/Frozen/Spec/IsIntegratedSLEEvolution_ae_exists_isGeneratingTrace.lean`.

The statement is the frozen anchor's with all arguments implicit and its hypotheses as auto-parameters (provider
convention); the proof is the closed provider
`InteractingSLE.Seal.Final.IsIntegratedSLEEvolution_ae_exists_isGeneratingTrace` (PROVE-T12-ASSEMBLE5, seal round).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Spec.Provider

theorem IsIntegratedSLEEvolution_ae_exists_isGeneratingTrace
    {a : ℝ} (ha : 0 < a := by assumption)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  by exact Seal.Final.IsIntegratedSLEEvolution_ae_exists_isGeneratingTrace

end InteractingSLE.Spec.Provider
