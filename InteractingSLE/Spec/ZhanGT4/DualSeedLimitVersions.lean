/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLimit
import InteractingSLE.Spec.ZhanGT4.DualJointMeas

/-!
# Continuous adapted versions from data before a stopping time

Packet PROVE-ZHAN-GT4-A22. A process continuous up to its finite stopping
horizon, and measurable there on each alive event, has a continuous adapted
stopped version. The random evaluation uses A16's measurable grid-limit lemma.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Evaluate a process at a capped stopping time using only its measurability
on the alive events and its pathwise continuity before the horizon. -/
theorem measurable_stopped_of_indicator {𝓕 : Filtration ℝ≥0 mΩ}
    {X : Ω → ℝ → ℝ} {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hXm : ∀ u : ℝ≥0, Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => X ω u))
    (hXc : ∀ ω, ContinuousOn (X ω) (Icc 0 (T ω))) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => X ω ((min t (T ω) : ℝ≥0) : ℝ) := by
  have hS : IsStoppingTime 𝓕 fun ω => ((min t (T ω) : ℝ≥0) : WithTop ℝ≥0) := by
    simpa only [WithTop.coe_min] using (isStoppingTime_const 𝓕 t).min hT
  have hSm : Measurable[𝓕 t] fun ω => min t (T ω) := by
    have hm := (hS.measurable_of_le
      (fun ω => WithTop.coe_le_coe.2 (min_le_left t (T ω)))).untopA
    simpa only [WithTop.untopA, WithTop.untopD_coe] using hm
  let S : Ω → ℝ := fun ω => ((min t (T ω) : ℝ≥0) : ℝ)
  have hSr : Measurable[𝓕 t] S := measurable_coe_nnreal_real.comp hSm
  apply @measurable_comp_of_sepCont Ω (𝓕 t) (fun ω x _ => X ω x) S (fun _ => 0)
    hSr measurable_const (fun ω => NNReal.coe_nonneg _) (fun _ => le_rfl)
  · intro x y hx hy
    by_cases hy0 : y ≤ 0
    swap
    · simpa only [hy0, and_false, Set.ofPred_false, indicator_empty] using
        (measurable_const : Measurable[𝓕 t] (fun _ : Ω => (0 : ℝ)))
    by_cases hxt : x ≤ t
    swap
    · have he : {ω | x ≤ S ω ∧ y ≤ (0 : ℝ)} = ∅ := by
        apply eq_empty_iff_forall_notMem.2
        intro ω hω
        exact hxt (hω.1.trans (NNReal.coe_le_coe.2 (min_le_left _ _)))
      rw [he, indicator_empty]
      exact measurable_const
    have hqt : x.toNNReal ≤ t := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hxt
    have hfm : Measurable[𝓕 t] ({ω | x.toNNReal ≤ T ω}.indicator fun ω => X ω x) := by
      simpa only [Real.coe_toNNReal _ hx] using
        (hXm x.toNNReal).mono (𝓕.mono hqt) le_rfl
    have hEm : MeasurableSet[𝓕 t] {ω | x ≤ S ω ∧ y ≤ (0 : ℝ)} := by
      simpa only [hy0, and_true] using (measurableSet_le measurable_const hSr)
    have hsub : {ω | x ≤ S ω ∧ y ≤ (0 : ℝ)} ⊆ {ω | x.toNNReal ≤ T ω} := by
      intro ω hω
      change x.toNNReal ≤ T ω
      rw [Real.toNNReal_le_iff_le_coe]
      exact hω.1.trans (NNReal.coe_le_coe.2 (min_le_right _ _))
    have hi := Measurable.indicator (m := 𝓕 t) hfm hEm
    rw [indicator_indicator, inter_eq_left.2 hsub] at hi
    exact hi
  · intro ω y _
    exact (hXc ω).mono (Icc_subset_Icc_right (NNReal.coe_le_coe.2 (min_le_right _ _)))
  · intro ω
    exact continuousOn_const

/-- The stopped version is continuous on the whole nonnegative time line. -/
theorem continuous_stopped_of_continuousOn {X : Ω → ℝ → ℝ} {T : Ω → ℝ≥0}
    (hXc : ∀ ω, ContinuousOn (X ω) (Icc 0 (T ω))) (ω : Ω) :
    Continuous (fun u : ℝ≥0 => X ω ((min u (T ω) : ℝ≥0) : ℝ)) := by
  apply (hXc ω).comp_continuous
    (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
  intro u
  exact ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_right _ _)⟩

/-- A finite family of gap processes obtains exactly the continuous adapted
versions required by `integral_indicator_mul_seed_band_eq_zero`. -/
theorem exists_continuous_adapted_stopped_versions {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ} {X : ι → Ω → ℝ → ℝ} {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hXm : ∀ i (u : ℝ≥0),
      Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => X i ω u))
    (hXc : ∀ i ω, ContinuousOn (X i ω) (Icc 0 (T ω))) :
    ∃ Y : ι → ℝ≥0 → Ω → ℝ,
      (∀ i ω, Continuous (Y i · ω)) ∧
      (∀ i u, Measurable[𝓕 u] (Y i u)) ∧
      ∀ i ω u, u ≤ T ω → Y i u ω = X i ω u := by
  refine ⟨fun i u ω => X i ω ((min u (T ω) : ℝ≥0) : ℝ), ?_, ?_, ?_⟩
  · exact fun i => continuous_stopped_of_continuousOn (hXc i)
  · exact fun i u => measurable_stopped_of_indicator hT (hXm i) (hXc i) u
  · intro i ω u hu
    dsimp only
    rw [min_eq_left hu]

end InteractingSLE.ZhanGT4
