/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchMeyerAnnounce

/-!
# Lifetime rules from predictable-time lifting

The sole named input below is the standard predictable-time lifting theorem,
in announcing-sequence form: Dellacherie--Meyer, Probabilities and Potential,
Ch. IV, Thm. 78 and the following comments. It is also stated as Theorem 3.1(1)
of Beiglböck--Cox--Huesmann, Inventiones 208 (2017), 327--400. This input has no
SLE, history-space or Galmarino conclusion and is not asserted here.

The stopped model already announces its lifetime. Lift that announcement to
the raw history filtration, record complete paths, and take the supremum of
the resulting raw stopping times. Its positive guarded history rule represents
the original lifetime. Predictability of arbitrary pre-lifetime stops is not
needed for this argument.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchMeyer

open LawUnique Restart.RetAux79 Restart.StoppedExtendWF RetMatchRaw RetMatchGal
open RetMatchLift RetMatchPredict Sec7.PocketTraversal

/-- The standard augmentation-removal theorem for predictable times, expressed
using finite announcing sequences. A raw predictable version of the announced
time supplies the sequence in the conclusion; equality of the times is only
a.e. No stochastic regularization theorem is assumed for arbitrary stops. -/
def PredictableAnnouncingLiftingStatement : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (V : Ω → ℝ≥0∞) (A : ℕ → Ω → ℝ≥0),
    Measurable V → Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P V A →
      ∃ B : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq 𝓕 P V B

/-- The model's existing bounded announcements have everywhere finite real
versions, still strictly announcing its lifetime in the driving filtration. -/
theorem exists_model_lifetime_announcingSeq {κ θ : ℝ} (M : StoppedTypeModel κ θ) :
    ∃ A : ℕ → M.space → ℝ≥0,
      Coupling.IsAnnouncingSeq (drivingFiltration M.law M.data.killedMeas) M.law
        M.data.life A := by
  let A : ℕ → M.space → ℝ≥0 := fun n ω =>
    ENNReal.toNNReal (boundedDriveStop M n ω : ℝ≥0∞)
  have he : ∀ n ω, (A n ω : ℝ≥0∞) = (boundedDriveStop M n ω : ℝ≥0∞) := by
    intro n ω
    exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top
      (boundedDriveStop_le M n ω))
  have hs : ∀ n, IsStoppingTime (drivingFiltration M.law M.data.killedMeas)
      (fun ω => (A n ω : WithTop ℝ≥0)) := by
    intro n
    have he' : (fun ω => (A n ω : WithTop ℝ≥0)) = boundedDriveStop M n :=
      funext fun ω => congrArg (fun x : ℝ≥0∞ => (x : WithTop ℝ≥0)) (he n ω)
    exact he'.symm ▸ isStoppingTime_boundedDriveStop M n
  refine ⟨A, hs, ?_, ?_, ?_⟩
  · intro ω n k hnk
    exact ENNReal.coe_le_coe.1 ((he n ω).trans_le
      ((monotone_boundedDriveStop M ω hnk).trans_eq (he k ω).symm))
  · intro n
    filter_upwards [ae_boundedDriveStop_bounds M] with ω hω
    exact (he n ω).symm ▸ (hω n).2
  · filter_upwards [ae_tendsto_boundedDriveStop M] with ω hω
    intro t ht
    obtain ⟨n, hn⟩ := (hω.eventually (lt_mem_nhds ht)).exists
    exact ⟨n, (ENNReal.coe_lt_coe.1 ((he n ω).trans_gt hn)).le⟩

/-- In particular, the canonical lifetime coordinate is already predictable
under the canonical usual augmentation. This uses only the supplied model. -/
theorem exists_canonical_lifetime_announcingSeq {κ θ : ℝ} (M : StoppedTypeModel κ θ) :
    ∃ A : ℕ → HistorySpace M.data.nL M.data.nR → ℝ≥0,
      Coupling.IsAnnouncingSeq (usualAugmentation historyFiltration (modelHistoryLaw M))
        (modelHistoryLaw M) Prod.fst A := by
  obtain ⟨A, hA⟩ := exists_model_lifetime_announcingSeq M
  obtain ⟨a, ha, _⟩ := exists_canonical_announcingSeq M measurable_fst hA
  exact ⟨a, ha⟩

/-- A raw announcement of the canonical lifetime yields its global history
rule. The supremum is taken on complete state paths before applying the guard,
so zero individual announcing times cause no difficulty. -/
theorem hasStoppedTypeHistoryRule_of_rawLifetimeAnnouncement
    {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    {B : ℕ → HistorySpace M.data.nL M.data.nR → ℝ≥0}
    (hB : Coupling.IsAnnouncingSeq historyFiltration (modelHistoryLaw M) Prod.fst B) :
    HasStoppedTypeHistoryRule M := by
  let τ : (ℝ≥0 → DrivingValue M.data.nL M.data.nR) → ℝ≥0∞ :=
    fun w => ⨆ n, (B n (fullHistory w) : ℝ≥0∞)
  have hBm : ∀ n, Measurable fun γ => (B n γ : ℝ≥0∞) :=
    fun n => (hB.1 n).measurable'
  have hτm : Measurable τ := Measurable.iSup fun n =>
    (hBm n).comp measurable_fullHistory
  have hτ : IsStoppingTime statePathFiltration (fun w => (τ w : WithTop ℝ≥0)) := by
    intro t
    have heq : {w | (τ w : WithTop ℝ≥0) ≤ t} =
        ⋂ n, {w | (B n (fullHistory w) : WithTop ℝ≥0) ≤ t} := by
      ext w
      change (⨆ n, (B n (fullHistory w) : ℝ≥0∞)) ≤ (t : ℝ≥0∞) ↔ _
      simp only [iSup_le_iff, mem_iInter, mem_ofPred_eq, ENNReal.coe_le_coe,
        WithTop.coe_le_coe]
    exact heq.symm ▸ (MeasurableSet.iInter fun n =>
      isStoppingTime_fullHistory (hB.1 n) t)
  have hsup : ∀ᵐ γ ∂modelHistoryLaw M, (⨆ n, (B n γ : ℝ≥0∞)) = γ.1 := by
    filter_upwards [ae_tendsto_of_isAnnouncingSeq hB] with γ hγ
    have hm : Monotone fun n => (B n γ : ℝ≥0∞) :=
      fun n k hnk => ENNReal.coe_le_coe.2 (hB.2.1 γ hnk)
    exact tendsto_nhds_unique (tendsto_atTop_iSup hm) hγ
  have he : ∀ᵐ ω ∂M.law, τ (fun t => (M.data.driver t ω,
      fun i => geomLW M.data.driver M.data.xL i t ω,
      fun j => geomRW M.data.driver M.data.xR j t ω)) = M.data.life ω := by
    have hlt' := ae_of_ae_map (measurable_modelHistory M).aemeasurable
      (ae_all_iff.2 hB.2.2.1)
    have hsup' := ae_of_ae_map (measurable_modelHistory M).aemeasurable hsup
    filter_upwards [hlt', hsup'] with ω hltω hsupω
    exact (iSup_congr fun n => rawStop_fullHistory_eq_killedHistory (hB.1 n)
      (continuous_modelState M ω) (hltω n)).trans hsupω
  refine ⟨ruleOfRawStop τ, measurable_ruleOfRawStop hτm,
    isHistGalmarino_ruleOfRawStop hτ, ?_⟩
  filter_upwards [he, M.data.lifePos] with ω heω hposω
  exact heω.symm.trans (ruleOfRawStop_killedHistory hτ (continuous_modelState M ω)
    (heω.symm ▸ hposω) heω.le).symm

/-- One standard predictable-time lifting input supplies every stopped model's
lifetime rule. No local SLE filtration-identification hypothesis is added. -/
theorem hasStoppedTypeHistoryRule_of_predictableLifting
    (hMeyer : PredictableAnnouncingLiftingStatement)
    {κ θ : ℝ} (M : StoppedTypeModel κ θ) : HasStoppedTypeHistoryRule M := by
  let _ := M.probability
  let _ : IsProbabilityMeasure (modelHistoryLaw M) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_modelHistory M).aemeasurable).2
      inferInstance
  obtain ⟨A, hA⟩ := exists_canonical_lifetime_announcingSeq M
  obtain ⟨B, hB⟩ := hMeyer _ (modelHistoryLaw M) historyFiltration Prod.fst A measurable_fst hA
  exact hasStoppedTypeHistoryRule_of_rawLifetimeAnnouncement M hB

end InteractingSLE.Wire.RetMatchMeyer
