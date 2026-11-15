import InteractingSLE.Spec.Sec2.Assembly2Entr
import InteractingSLE.Spec.Coupling.ResampleProjBridge

/-!
# Provider for the frozen anchor `InteractingSLE/Frozen/Spec/exists_isOptionalHullCoupling.lean`

**Theorem 1.1** (Specification p. 9), by the route of ruling R35 (Astra's §1): the coupling is assembled in
`InteractingSLE.Spec.Coupling.ResampleProjBridge` (`Coupling.exists_isOptionalHullCoupling_of_thm22`, packets PROVE-T11-*), whose
only input — the existence half of Theorem 2.2 — is `InteractingSLE.exists_isIntegratedSLEEvolution_assembled`
(`InteractingSLE.Spec.Sec2.Assembly2Entr`). The statement below is the frozen anchor's with all arguments implicit and its
hypotheses as auto-parameters (provider convention).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Spec.Provider

theorem exists_isOptionalHullCoupling {κ : ℝ} (hκ : 0 < κ := by assumption) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h :=
  InteractingSLE.Coupling.exists_isOptionalHullCoupling_of_thm22 hκ hF
    (InteractingSLE.exists_isIntegratedSLEEvolution_assembled hκ hF)

end InteractingSLE.Spec.Provider
