/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchGalRule
import InteractingSLE.Spec.Wire.RetMatchGalSDE

/-!
# The canonical Galmarino witness from a concrete raw stopping-time version

This finishes the deterministic and measure-transport part of the existing
canonical regularization goal. It takes an actual raw stopping-time version,
constructs the witness by `ruleOfRawStop`, and verifies all of its properties.
No new universal regularization hypothesis is introduced. The existence of
that raw version for an arbitrary canonical augmented stopping time remains
unproved; in particular the original canonical statement is not asserted.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchGal

open Restart.RetAux79 Restart.StoppedExtendWF LawUnique Sec7.PocketTraversal RetMatchRaw

/-- A concrete raw stopping-time version supplies the complete canonical
Galmarino conclusion. No boundedness or further regularity is needed for this
construction beyond the original almost-sure positive pre-lifetime bound. -/
theorem exists_canonicalHistoryRule_of_rawStop
    {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    {s : HistorySpace M.data.nL M.data.nR → ℝ≥0} (hsm : Measurable s)
    (hpre : ∀ᵐ γ ∂modelHistoryLaw M, 0 < (s γ : ℝ≥0∞) ∧ (s γ : ℝ≥0∞) < γ.1)
    {τ : (ℝ≥0 → DrivingValue M.data.nL M.data.nR) → ℝ≥0∞}
    (hτm : Measurable τ)
    (hτ : IsStoppingTime statePathFiltration (fun w => (τ w : WithTop ℝ≥0)))
    (he : ∀ᵐ ω ∂M.law, (s (modelHistory M ω) : ℝ≥0∞) = τ (fun t =>
      (M.data.driver t ω, fun i => geomLW M.data.driver M.data.xL i t ω,
        fun j => geomRW M.data.driver M.data.xR j t ω))) :
    ∃ Q : HistorySpace M.data.nL M.data.nR → ℝ≥0∞,
      Measurable Q ∧ IsHistGalmarino Q ∧
        ∀ᵐ γ ∂modelHistoryLaw M, (s γ : ℝ≥0∞) = Q γ := by
  refine ⟨ruleOfRawStop τ, measurable_ruleOfRawStop hτm,
    isHistGalmarino_ruleOfRawStop hτ, ?_⟩
  apply (ae_map_iff (measurable_modelHistory M).aemeasurable
    (measurableSet_eq_fun (measurable_coe_nnreal_ennreal.comp hsm)
      (measurable_ruleOfRawStop hτm))).2
  have hp := ae_of_ae_map (measurable_modelHistory M).aemeasurable hpre
  filter_upwards [he, hp] with ω heω hpω
  have hbounds : 0 < τ (fun t => (M.data.driver t ω,
      fun i => geomLW M.data.driver M.data.xL i t ω,
      fun j => geomRW M.data.driver M.data.xR j t ω)) ∧
      τ (fun t => (M.data.driver t ω,
        fun i => geomLW M.data.driver M.data.xL i t ω,
        fun j => geomRW M.data.driver M.data.xR j t ω)) ≤ M.data.life ω :=
    heω ▸ ⟨hpω.1, hpω.2.le⟩
  exact heω.trans (ruleOfRawStop_killedHistory hτ (continuous_modelState M ω)
    hbounds.1 hbounds.2).symm

end InteractingSLE.Wire.RetMatchGal
