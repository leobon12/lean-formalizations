import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# Provider for the frozen anchor `InteractingSLE/Frozen/Spec/exists_isIntegratedSLEEvolution.lean`

**Theorem 2.2, existence** (Specification p. 21), assembled in `InteractingSLE.Spec.Sec2.Assembly2Entr`
(packet PROVE-SEC2-PATCH3): `InteractingSLE.exists_isIntegratedSLEEvolution_assembled`. The statement below is the
frozen anchor's with all arguments implicit and its hypotheses as auto-parameters (provider convention), so the anchor's
proof is the bare `by exact InteractingSLE.Spec.Provider.exists_isIntegratedSLEEvolution`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Spec.Provider

theorem exists_isIntegratedSLEEvolution {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ :=
  InteractingSLE.exists_isIntegratedSLEEvolution_assembled ha hF

end InteractingSLE.Spec.Provider
