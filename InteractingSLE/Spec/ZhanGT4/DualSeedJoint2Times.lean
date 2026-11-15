/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualJointMeas
import InteractingSLE.Spec.ZhanGT4.A1PatchStair

/-!
# Measurability at random times inside one protected rectangle

PROVE-ZHAN-GT4-A22. Reuses the existing dyadic rounding theorem. Fixed-time
measurability is only required on the actual random rectangle, and separate
continuity is only required there, including its zero sides.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4.A1Patch

/-- A fixed-time measurable, separately continuous rectangle field is measurable
at every pair of measurable times in that rectangle. -/
theorem isFieldMeas_of_fixed_and_sepCont {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {N : X × Y → ℝ → ℝ → ℝ} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0}
    (hm : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      Measurable ({ω : X × Y | s ≤ S₁ ω.1 ∧ t ≤ S₂ ω.2}.indicator fun ω => N ω s t))
    (hc₁ : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (S₂ ω.2),
      ContinuousOn (fun s => N ω s t) (Icc (0 : ℝ) (S₁ ω.1)))
    (hc₂ : ∀ ω, ∀ s ∈ Icc (0 : ℝ) (S₁ ω.1),
      ContinuousOn (fun t => N ω s t) (Icc (0 : ℝ) (S₂ ω.2))) :
    IsFieldMeas N (fun _ : Unit => S₁) (fun _ : Unit => S₂) := by
  intro U V hU hV hU0 hV0 hUV
  have hle : ∀ ω, U ω ≤ S₁ ω.1 ∧ V ω ≤ S₂ ω.2 := fun ω => (hUV ω).choose_spec
  refine measurable_comp_of_sepCont hU hV hU0 hV0 (fun s t hs ht => ?_)
    (fun ω t ht => (hc₁ ω t ⟨ht.1, ht.2.trans (hle ω).2⟩).mono
      (Icc_subset_Icc_right (hle ω).1))
    (fun ω => (hc₂ ω (U ω) ⟨hU0 ω, (hle ω).1⟩).mono
      (Icc_subset_Icc_right (hle ω).2))
  have hG : MeasurableSet {ω | s ≤ U ω ∧ t ≤ V ω} :=
    (measurableSet_le measurable_const hU).inter (measurableSet_le measurable_const hV)
  have hsub : {ω | s ≤ U ω ∧ t ≤ V ω} ⊆
      {ω : X × Y | s ≤ S₁ ω.1 ∧ t ≤ S₂ ω.2} :=
    fun ω hω => ⟨hω.1.trans (hle ω).1, hω.2.trans (hle ω).2⟩
  convert (hm s t hs ht).indicator hG using 1
  funext ω
  by_cases hω : ω ∈ {ω | s ≤ U ω ∧ t ≤ V ω}
  · simp only [indicator_of_mem hω, indicator_of_mem (hsub hω)]
  · simp only [indicator_of_notMem hω]

/-- Stopped continuous nonnegative-time paths give continuity on the real
protected interval, including its endpoints. -/
theorem continuousOn_of_continuous_stopped {f : ℝ → ℝ} {T : ℝ≥0}
    (hc : Continuous fun u : ℝ≥0 => f (min (u : ℝ) T)) :
    ContinuousOn f (Icc (0 : ℝ) T) := by
  have h := hc.comp continuous_real_toNNReal
  refine h.continuousOn.congr fun u hu => ?_
  change f u = f (min (u.toNNReal : ℝ) T)
  rw [Real.coe_toNNReal _ hu.1, min_eq_left hu.2]

end InteractingSLE.ZhanGT4.A1Patch
