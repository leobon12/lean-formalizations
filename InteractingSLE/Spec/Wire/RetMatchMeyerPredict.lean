/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchMeyerLifetime

/-!
# Canonical pre-lifetime regularization for an announced stopping time

This applies the precise standard lifting input to a concrete announcing
sequence. The existing raw-history bridge then supplies the full conclusion
of canonical regularization. The existence of an announcement of an arbitrary
pre-lifetime stopping time is not asserted. The lifetime application in the
preceding file already has its announcement from the original model.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchMeyer

open LawUnique Restart.RetAux79 Restart.StoppedExtendWF RetMatchRaw

/-- From the standard predictable-time lifting input, an actual announced time
has a measurable raw stopping-time version, with equality only almost surely. -/
theorem exists_rawStop_of_announcingSeq
    (hMeyer : PredictableAnnouncingLiftingStatement)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    {A : ℕ → Ω → ℝ≥0} (hA : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P V A) :
    ∃ τ : Ω → ℝ≥0∞, Measurable τ ∧
      IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) ∧ ∀ᵐ ω ∂P, V ω = τ ω := by
  obtain ⟨B, hB⟩ := hMeyer Ω P 𝓕 V A hVm hA
  let τ : Ω → ℝ≥0∞ := fun ω => ⨆ n, (B n ω : ℝ≥0∞)
  have hBm : ∀ n, Measurable fun ω => (B n ω : ℝ≥0∞) :=
    fun n => (hB.1 n).measurable'
  refine ⟨τ, Measurable.iSup hBm, ?_, ?_⟩
  · intro t
    have heq : {ω | (τ ω : WithTop ℝ≥0) ≤ t} =
        ⋂ n, {ω | (B n ω : WithTop ℝ≥0) ≤ t} := by
      ext ω
      change (⨆ n, (B n ω : ℝ≥0∞)) ≤ (t : ℝ≥0∞) ↔ _
      simp only [iSup_le_iff, mem_iInter, mem_ofPred_eq, ENNReal.coe_le_coe,
        WithTop.coe_le_coe]
    exact heq.symm ▸ MeasurableSet.iInter (fun n => hB.1 n t)
  · filter_upwards [ae_tendsto_of_isAnnouncingSeq hB] with ω hω
    have hm : Monotone fun n => (B n ω : ℝ≥0∞) :=
      fun n k hnk => ENNReal.coe_le_coe.2 (hB.2.1 ω hnk)
    exact (tendsto_nhds_unique (tendsto_atTop_iSup hm) hω).symm

/-- The precise canonical Galmarino conclusion follows for every canonical
stop supplied with an announcement, using only the standard lifting input. -/
theorem exists_canonicalHistoryRule_of_announcingSeq
    (hMeyer : PredictableAnnouncingLiftingStatement)
    {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    {s : HistorySpace M.data.nL M.data.nR → ℝ≥0} (hsm : Measurable s)
    (hpre : ∀ᵐ γ ∂modelHistoryLaw M, 0 < (s γ : ℝ≥0∞) ∧ (s γ : ℝ≥0∞) < γ.1)
    {A : ℕ → HistorySpace M.data.nL M.data.nR → ℝ≥0}
    (hA : Coupling.IsAnnouncingSeq (usualAugmentation historyFiltration (modelHistoryLaw M))
      (modelHistoryLaw M) (fun γ => (s γ : ℝ≥0∞)) A) :
    ∃ Q : HistorySpace M.data.nL M.data.nR → ℝ≥0∞,
      Measurable Q ∧ IsHistGalmarino Q ∧
        ∀ᵐ γ ∂modelHistoryLaw M, (s γ : ℝ≥0∞) = Q γ := by
  let _ := M.probability
  let _ : IsProbabilityMeasure (modelHistoryLaw M) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_modelHistory M).aemeasurable).2
      inferInstance
  obtain ⟨τ, hτm, hτ, he⟩ := exists_rawStop_of_announcingSeq hMeyer
    (modelHistoryLaw M) historyFiltration (measurable_coe_nnreal_ennreal.comp hsm) hA
  exact exists_canonicalHistoryRule_of_rawHistoryStop M hsm hpre hτm hτ he

/-- It suffices to supply the announcement on the original model. Canonical
factorization and the globally monotone correction are already proved. -/
theorem exists_canonicalHistoryRule_of_modelAnnouncement
    (hMeyer : PredictableAnnouncingLiftingStatement)
    {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    {s : HistorySpace M.data.nL M.data.nR → ℝ≥0} (hsm : Measurable s)
    (hpre : ∀ᵐ γ ∂modelHistoryLaw M, 0 < (s γ : ℝ≥0∞) ∧ (s γ : ℝ≥0∞) < γ.1)
    {A : ℕ → M.space → ℝ≥0}
    (hA : Coupling.IsAnnouncingSeq (drivingFiltration M.law M.data.killedMeas) M.law
      (fun ω => (s (modelHistory M ω) : ℝ≥0∞)) A) :
    ∃ Q : HistorySpace M.data.nL M.data.nR → ℝ≥0∞,
      Measurable Q ∧ IsHistGalmarino Q ∧
        ∀ᵐ γ ∂modelHistoryLaw M, (s γ : ℝ≥0∞) = Q γ := by
  obtain ⟨a, ha, _⟩ := exists_canonical_announcingSeq M
    (measurable_coe_nnreal_ennreal.comp hsm) hA
  exact exists_canonicalHistoryRule_of_announcingSeq hMeyer M hsm hpre ha

end InteractingSLE.Wire.RetMatchMeyer
