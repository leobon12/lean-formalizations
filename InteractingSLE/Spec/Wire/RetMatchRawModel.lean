/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchRawHistory

/-!
# Positive bounded model stops factor through the history law

The factor on history space is everywhere finite and deterministically bounded.
It remains a stopping time of the canonical usual augmentation. Positivity and
strict pre-lifetime stopping hold almost surely under the canonical image law.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchRaw

open Restart.RetAux79 LawUnique Sec7.PocketTraversal

variable {κ θ : ℝ}

/-- The model's measurable killed driving history. -/
def modelHistory (M : StoppedTypeModel κ θ) : M.space → HistorySpace M.data.nL M.data.nR :=
  killedHistory M.data.driver (geomLW M.data.driver M.data.xL)
    (geomRW M.data.driver M.data.xR) M.data.life

theorem measurable_modelHistory (M : StoppedTypeModel κ θ) : Measurable (modelHistory M) :=
  measurable_killedHistory M.data.killedMeas

/-- The canonical law of the model's killed driving history. -/
def modelHistoryLaw (M : StoppedTypeModel κ θ) : Measure (HistorySpace M.data.nL M.data.nR) :=
  M.law.map (modelHistory M)

/-- The state used in a stopped model is continuous before its lifetime. -/
theorem continuousOn_modelState (M : StoppedTypeModel κ θ) (ω : M.space) :
    ContinuousOn
      (fun t => (M.data.driver t ω, fun i => geomLW M.data.driver M.data.xL i t ω,
        fun j => geomRW M.data.driver M.data.xR j t ω))
      {t | (t : ℝ≥0∞) < M.data.life ω} :=
  (M.data.driverCont ω).continuousOn.prodMk
    ((continuousOn_pi.2 fun i =>
      (isForcePath_geomLW M.data.driverCont M.data.xL ω i).1.continuousOn).prodMk
      (continuousOn_pi.2 fun j =>
        (isForcePath_geomRW M.data.driverCont M.data.xR ω j).1.continuousOn))

/-- A positive bounded pre-lifetime stop factors as a positive bounded
pre-lifetime stopping time on history space. Only the usual augmentation is
claimed; no pointwise Galmarino regularization is implicit. -/
theorem exists_bounded_history_stop (M : StoppedTypeModel κ θ)
    {σ : M.space → WithTop ℝ≥0} {b : ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration M.law M.data.killedMeas) σ)
    (hb : ∀ ω, (σ ω : ℝ≥0∞) ≤ (b : ℝ≥0∞))
    (hpre : ∀ᵐ ω ∂M.law, 0 < (σ ω : ℝ≥0∞) ∧ (σ ω : ℝ≥0∞) < M.data.life ω) :
    ∃ s : HistorySpace M.data.nL M.data.nR → ℝ≥0, Measurable s ∧
      IsStoppingTime (usualAugmentation historyFiltration (modelHistoryLaw M))
        (fun γ => (s γ : WithTop ℝ≥0)) ∧
      (∀ γ, s γ ≤ b) ∧
      (∀ᵐ γ ∂modelHistoryLaw M, 0 < (s γ : ℝ≥0∞) ∧ (s γ : ℝ≥0∞) < γ.1) ∧
      ∀ᵐ ω ∂M.law, σ ω = (s (modelHistory M ω) : WithTop ℝ≥0) := by
  have hfin : ∀ᵐ ω ∂M.law, σ ω ≠ ⊤ := ae_of_all _ fun ω =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (show σ ω ≤ (b : WithTop ℝ≥0) from hb ω)
  obtain ⟨s, hsm, hs, he⟩ := exists_isStoppingTime_ae_eq_history M.data.killedMeas
    (ae_of_all _ (continuousOn_modelState M)) hσ hfin
  let s' : HistorySpace M.data.nL M.data.nR → ℝ≥0 := fun γ => min (s γ) b
  have hs'm : Measurable s' := hsm.min measurable_const
  have hs' : IsStoppingTime (usualAugmentation historyFiltration (modelHistoryLaw M))
      (fun γ => (s' γ : WithTop ℝ≥0)) := by
    have hcap : IsStoppingTime (usualAugmentation historyFiltration (modelHistoryLaw M))
        (fun γ => min (s γ : WithTop ℝ≥0) (b : WithTop ℝ≥0)) := hs.min_const b
    have heq : (fun γ => (s' γ : WithTop ℝ≥0)) =
        fun γ => min (s γ : WithTop ℝ≥0) (b : WithTop ℝ≥0) :=
      funext fun γ => WithTop.coe_min (s γ) b
    exact heq.symm ▸ hcap
  have he' : ∀ᵐ ω ∂M.law, σ ω = (s' (modelHistory M ω) : WithTop ℝ≥0) := by
    filter_upwards [he] with ω heω
    have hsb : s (modelHistory M ω) ≤ b :=
      WithTop.coe_le_coe.1 (heω ▸ (show σ ω ≤ (b : WithTop ℝ≥0) from hb ω))
    exact heω.trans (congrArg (fun t : ℝ≥0 => (t : WithTop ℝ≥0)) (min_eq_left hsb).symm)
  refine ⟨s', hs'm, hs', fun γ => min_le_right _ _, ?_, he'⟩
  have hset : MeasurableSet {γ : HistorySpace M.data.nL M.data.nR |
      0 < (s' γ : ℝ≥0∞) ∧ (s' γ : ℝ≥0∞) < γ.1} :=
    (measurableSet_lt measurable_const (measurable_coe_nnreal_ennreal.comp hs'm)).inter
      (measurableSet_lt (measurable_coe_nnreal_ennreal.comp hs'm) measurable_fst)
  apply (ae_map_iff (measurable_modelHistory M).aemeasurable hset).2
  filter_upwards [he', hpre] with ω heω hpω
  have hee : (σ ω : ℝ≥0∞) = (s' (modelHistory M ω) : ℝ≥0∞) :=
    congrArg (fun t : WithTop ℝ≥0 => (t : ℝ≥0∞)) heω
  exact hee ▸ hpω

end InteractingSLE.Wire.RetMatchRaw
