/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchMeyerRule

/-!
# Announcing sequences descend to canonical history space

Factor each finite announcing time by the existing stopping-time Doob--Dynkin
theorem. Taking partial suprema repairs monotonicity on every history, including
histories outside the image law. The strict inequalities and supremum identity
are Borel events and descend under the image law. Thus predictability may be
proved on the original stopped model; no separate canonical version is needed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchMeyer

open LawUnique Restart.RetAux79 RetMatchRaw

/-- A finite announcing sequence in the model's own driving filtration
transfers to its canonical history law, with pointwise monotonicity preserved. -/
theorem exists_canonical_announcingSeq
    {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    {v : HistorySpace M.data.nL M.data.nR → ℝ≥0∞} (hvm : Measurable v)
    {A : ℕ → M.space → ℝ≥0}
    (hA : Coupling.IsAnnouncingSeq (drivingFiltration M.law M.data.killedMeas) M.law
      (fun ω => v (modelHistory M ω)) A) :
    ∃ a : ℕ → HistorySpace M.data.nL M.data.nR → ℝ≥0,
      Coupling.IsAnnouncingSeq (usualAugmentation historyFiltration (modelHistoryLaw M))
        (modelHistoryLaw M) v a ∧
      ∀ᵐ ω ∂M.law, ∀ n, a n (modelHistory M ω) = A n ω := by
  have hex : ∀ n, ∃ a : HistorySpace M.data.nL M.data.nR → ℝ≥0,
      Measurable a ∧
      IsStoppingTime (usualAugmentation historyFiltration (modelHistoryLaw M))
        (fun γ => (a γ : WithTop ℝ≥0)) ∧
      ∀ᵐ ω ∂M.law, A n ω = a (modelHistory M ω) := by
    intro n
    obtain ⟨a, ham, ha, he⟩ := exists_isStoppingTime_ae_eq_history M.data.killedMeas
      (ae_of_all _ (continuousOn_modelState M)) (hA.1 n)
      (ae_of_all _ fun _ => WithTop.coe_ne_top)
    refine ⟨a, ham, ha, ?_⟩
    filter_upwards [he] with ω hω
    exact WithTop.coe_injective hω
  choose a ham ha he using hex
  let b : ℕ → HistorySpace M.data.nL M.data.nR → ℝ≥0 := fun n γ =>
    partialSups (fun k => a k γ) n
  have hb_succ : ∀ n γ, b (n + 1) γ = max (b n γ) (a (n + 1) γ) :=
    fun n γ => partialSups_succ (fun k => a k γ) n
  have hbm : ∀ n, Measurable (b n) := by
    intro n
    induction n with
    | zero => simpa only [b, partialSups_zero] using ham 0
    | succ n ih =>
      exact (funext (hb_succ n)).symm ▸ ih.max (ham (n + 1))
  have hbs : ∀ n, IsStoppingTime
      (usualAugmentation historyFiltration (modelHistoryLaw M))
      (fun γ => (b n γ : WithTop ℝ≥0)) := by
    intro n
    induction n with
    | zero => simpa only [b, partialSups_zero] using ha 0
    | succ n ih =>
      have hh := ih.max (ha (n + 1))
      have hh' : (fun γ => (b (n + 1) γ : WithTop ℝ≥0)) =
          fun γ => max (b n γ : WithTop ℝ≥0) (a (n + 1) γ : WithTop ℝ≥0) := by
        funext γ
        exact (congrArg (fun x : ℝ≥0 => (x : WithTop ℝ≥0)) (hb_succ n γ)).trans
          (WithTop.coe_max _ _)
      exact hh'.symm ▸ hh
  have hbe : ∀ᵐ ω ∂M.law, ∀ n, b n (modelHistory M ω) = A n ω := by
    filter_upwards [ae_all_iff.2 he] with ω hω
    intro n
    change partialSups (fun k => a k (modelHistory M ω)) n = A n ω
    have hf : (fun k => a k (modelHistory M ω)) = fun k => A k ω :=
      funext fun k => (hω k).symm
    rw [hf]
    exact congrFun (hA.2.1 ω).partialSups_eq n
  have hgoodm : MeasurableSet {γ | (∀ n, (b n γ : ℝ≥0∞) < v γ) ∧
      (⨆ n, (b n γ : ℝ≥0∞)) = v γ} := by
    have hlt : MeasurableSet {γ | ∀ n, (b n γ : ℝ≥0∞) < v γ} :=
      by
        simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun n => measurableSet_lt
          (measurable_coe_nnreal_ennreal.comp (hbm n)) hvm
    exact hlt.inter (measurableSet_eq_fun
      (Measurable.iSup fun n => measurable_coe_nnreal_ennreal.comp (hbm n))
      hvm)
  have hgood : ∀ᵐ γ ∂modelHistoryLaw M,
      (∀ n, (b n γ : ℝ≥0∞) < v γ) ∧
        (⨆ n, (b n γ : ℝ≥0∞)) = v γ := by
    apply (ae_map_iff (measurable_modelHistory M).aemeasurable hgoodm).2
    filter_upwards [hbe, ae_all_iff.2 hA.2.2.1, ae_tendsto_of_isAnnouncingSeq hA]
      with ω hbω hltω hlimω
    refine ⟨fun n => (congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (hbω n).symm) ▸ hltω n, ?_⟩
    have hm : Monotone fun n => (A n ω : ℝ≥0∞) :=
      fun n k hnk => ENNReal.coe_le_coe.2 (hA.2.1 ω hnk)
    have hsup := tendsto_nhds_unique (tendsto_atTop_iSup hm) hlimω
    exact (iSup_congr fun n => congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (hbω n)).trans hsup
  refine ⟨b, ⟨hbs, fun γ => (partialSups (fun k => a k γ)).monotone, ?_, ?_⟩, hbe⟩
  · intro n
    filter_upwards [hgood] with γ hγ
    exact hγ.1 n
  · filter_upwards [hgood] with γ hγ
    intro t ht
    have hlt : (t : ℝ≥0∞) < ⨆ n, (b n γ : ℝ≥0∞) := ht.trans_eq hγ.2.symm
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
    exact ⟨n, (ENNReal.coe_lt_coe.1 hn).le⟩

end InteractingSLE.Wire.RetMatchMeyer
