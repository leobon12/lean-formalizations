/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchRawModel

/-!
# The remaining regularization question is entirely on history space

The named input below concerns canonical history laws and their augmented
stopping times. The original sample-space factorization, deterministic cap,
and transport of almost-sure identities are proved. The equivalence with the
previous local input records that the new boundary adds no stronger assumption.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchRaw

open Restart.RetAux79 Restart.StoppedExtendWF LawUnique RetMatchPredict

/-- Unproved canonical regularization input: an augmented stopping time,
positive and strictly before death almost surely and bounded everywhere,
admits a measurable rule satisfying Galmarino on all continuous histories.
This is a named hypothesis, not an asserted regularization theorem. -/
def CanonicalPrelifeRegularizationStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ : ℝ, ∀ M : StoppedTypeModel κ θ,
    ∀ (s : HistorySpace M.data.nL M.data.nR → ℝ≥0) (b : ℝ≥0),
      Measurable s →
      IsStoppingTime (usualAugmentation historyFiltration (modelHistoryLaw M))
        (fun γ => (s γ : WithTop ℝ≥0)) →
      (∀ γ, s γ ≤ b) →
      (∀ᵐ γ ∂modelHistoryLaw M, 0 < (s γ : ℝ≥0∞) ∧ (s γ : ℝ≥0∞) < γ.1) →
      ∃ Q : HistorySpace M.data.nL M.data.nR → ℝ≥0∞,
        Measurable Q ∧ IsHistGalmarino Q ∧
          ∀ᵐ γ ∂modelHistoryLaw M, (s γ : ℝ≥0∞) = Q γ

/-- Canonical regularization supplies the previously named model-space input;
the required factorization is the unconditional bounded-history theorem. -/
theorem positiveBoundedPrelifeRuleStatement_of_canonicalRegularization
    (hC : CanonicalPrelifeRegularizationStatement) : PositiveBoundedPrelifeRuleStatement := by
  intro κ hκ hκ4 θ M σ b hσ hb hpre
  obtain ⟨s, hsm, hs, hsb, hsp, he⟩ := exists_bounded_history_stop M hσ hb hpre
  obtain ⟨Q, hQm, hQg, hQe⟩ := hC κ hκ hκ4 θ M s b hsm hs hsb hsp
  refine ⟨Q, hQm, hQg, ?_⟩
  have hQpull := ae_of_ae_map (measurable_modelHistory M).aemeasurable hQe
  filter_upwards [he, hQpull] with ω heω hQω
  exact (congrArg (fun t : WithTop ℝ≥0 => (t : ℝ≥0∞)) heω).trans hQω

/-- Conversely, the previous local input already implies canonical
regularization: pull the canonical stopping time back to the model and push
the resulting measurable almost-sure identity to its history law. -/
theorem canonicalPrelifeRegularizationStatement_of_positiveBoundedPrelifeRules
    (hLocal : PositiveBoundedPrelifeRuleStatement) : CanonicalPrelifeRegularizationStatement := by
  intro κ hκ hκ4 θ M s b hsm hs hsb hpre
  have hcomp := Exist.isStoppingTime_comp (measurable_modelHistory M) rfl hs
  have hf := drivingFiltration_eq_historyComap (P := M.law) M.data.killedMeas
    (ae_of_all _ (continuousOn_modelState M))
  have hσ : IsStoppingTime (drivingFiltration M.law M.data.killedMeas)
      (fun ω => (s (modelHistory M ω) : WithTop ℝ≥0)) := hf.symm ▸ hcomp
  have hb : ∀ ω : M.space, (s (modelHistory M ω) : ℝ≥0∞) ≤ (b : ℝ≥0∞) :=
    fun ω => ENNReal.coe_le_coe.2 (hsb (modelHistory M ω))
  have hp := ae_of_ae_map (measurable_modelHistory M).aemeasurable hpre
  obtain ⟨Q, hQm, hQg, he⟩ := hLocal κ hκ hκ4 θ M _ b hσ hb hp
  refine ⟨Q, hQm, hQg, ?_⟩
  exact (ae_map_iff (measurable_modelHistory M).aemeasurable
    (measurableSet_eq_fun (measurable_coe_nnreal_ennreal.comp hsm) hQm)).2 he

/-- The canonical input is exactly the remaining local representation gap. -/
theorem canonicalPrelifeRegularizationStatement_iff :
    CanonicalPrelifeRegularizationStatement ↔ PositiveBoundedPrelifeRuleStatement :=
  ⟨positiveBoundedPrelifeRuleStatement_of_canonicalRegularization,
    canonicalPrelifeRegularizationStatement_of_positiveBoundedPrelifeRules⟩

end InteractingSLE.Wire.RetMatchRaw
