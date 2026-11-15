/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndMarks
import InteractingSLE.Spec.Restart.RetPlumbProofInputsClock

/-!
# The image hull's compact-avoidance event is observable at a physical line

Packet PROVE-CFCHART2. Read the filled image prefix from the two stopped
histories. Masking outside the observable pre-contact event gives a continuous
path for every good stopped datum, so the landed filled-prefix measurability
applies even at the endpoint of the physical prefix.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfPhys

open WangWu LawUnique GlueCond Cond44Ref CfRegQ Prop411Q LocalSets
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Sec7.Lemma71C (capClock)

/-- The physical-line safety event for a compact set in the image coordinate. -/
def imageLineSafe {Ω : Type*} {nL nR : ℕ} (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (s : ℝ≥0) (E : Set (Ω × HistorySpace 0 0)) (C : Set ℂ) (t : ℝ≥0) : Set (Ω × HistorySpace 0 0) :=
  {p | (t : ℝ) ∈ qgPre W VL VR ζ s E p ∧
    Disjoint C (fwdHull (Ito.rpath fun r => qW W VL VR ζ s E r p)
      (capClock (qgCurve W s E p) t))}

/-- Compact avoidance by the filled image prefix is measurable on good stopped
histories, including the physical endpoint `t`. -/
theorem measurableSet_safe_stopped {nL nR : ℕ} {s : ℝ≥0} {t : ℚ} (ht : (0 : ℝ) ≤ t)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) :
    MeasurableSet {x : {y : Y47 nL nR // IsGoodD47 s t y} |
      (t : ℝ) ∈ PcD47 s x.1 ∧ Disjoint C (fillH (gammaD47 s x.1 '' Icc 0 t))} := by
  classical
  let A : Set {y : Y47 nL nR // IsGoodD47 s t y} := {x | (t : ℝ) ∈ PcD47 s x.1}
  have hA : MeasurableSet A := measurableSet_mem_PcD47 t ht le_rfl
  let Γ : {y : Y47 nL nR // IsGoodD47 s t y} → ℝ≥0 → ℂ := fun x r =>
    if x ∈ A then gammaD47 s x.1 (min (r : ℝ) t) else 0
  have hc : ∀ x, Continuous (Γ x) := by
    intro x
    by_cases hx : x ∈ A
    · simp only [Γ, hx, ↓reduceIte]
      exact (x.2.cont t ht le_rfl hx).comp_continuous
        (NNReal.continuous_coe.min continuous_const) fun r =>
          ⟨le_min r.coe_nonneg ht, min_le_right _ _⟩
    · simp only [Γ, hx, ↓reduceIte]
      exact continuous_const
  have hm : ∀ r : ℝ≥0, Measurable fun x => Γ x r := fun r =>
    Measurable.ite hA ((measurable_gammaD47 _).comp measurable_subtype_coe) measurable_const
  have hfill := Restart.RetAux79.measurable_fillH_image_Icc_of_prefix hc
    (fun r _ => hm r) (t := (t : ℝ).toNNReal)
  have hs : MeasurableSet {x | Disjoint C (fillH (Γ x '' Icc 0 (t : ℝ).toNNReal))} := by
    have h := hfill (measurableSet_disjoint_relClosureH hC hCH)
    convert h using 1
    ext x
    rw [mem_ofPred_eq, mem_preimage, mem_ofPred_eq,
      relClosureH_eq (fillH_subset_H _) (isOpen_H_diff_fillH (isCompact_Icc.image (hc x)).isBounded)]
  have he : {x : {y : Y47 nL nR // IsGoodD47 s t y} |
      (t : ℝ) ∈ PcD47 s x.1 ∧ Disjoint C (fillH (gammaD47 s x.1 '' Icc 0 t))} =
      A ∩ {x | Disjoint C (fillH (Γ x '' Icc 0 (t : ℝ).toNNReal))} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff]
    refine and_congr_right fun hx => ?_
    have himg : gammaD47 s x.1 '' Icc 0 t = Γ x '' Icc 0 (t : ℝ).toNNReal := by
      rw [Sec7.Lemma71E.image_Icc_real_eq ht]
      refine image_congr fun r hr => ?_
      have hrt : (r : ℝ) ≤ t := by
        have h := NNReal.coe_le_coe.2 hr.2
        rwa [Real.coe_toNNReal _ ht] at h
      simp only [Γ, show x ∈ A from hx, ↓reduceIte, min_eq_left hrt]
    rw [himg]
  rw [he]
  exact hA.inter hs

/-- The compact-avoidance event of the image hull has a version in the physical
stopped-history marks. This is the safety input for strict dyadic passage. -/
theorem imageLineSafe_marks {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}
    {μ : Measure (Ω × HistorySpace 0 0)} (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hgood : ∀ᵐ p ∂μ, p ∈ E) {t : ℚ} (ht : 0 < t) {C : Set ℂ}
    (hC : IsCompact C) (hCH : C ⊆ H) :
    ∃ B, MeasurableSet[CrossCond.cfGlueMarks W VL VR ζ s (t : ℝ).toNNReal] B ∧
      B =ᵐ[μ] imageLineSafe W VL VR ζ s E C (t : ℝ).toNNReal := by
  have ht0 : (0 : ℝ) ≤ t := by exact_mod_cast ht.le
  obtain ⟨S, hS, hSe⟩ := exists_measurableSet_of_subtypeD47 (measurableSet_safe_stopped ht0 hC hCH)
  refine ⟨stopD47 W VL VR ζ s t ⁻¹' S, measurable_stopD47 s t hS, ?_⟩
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hgood] with p hp
  have hg := hEg p hp
  have hgD := isGoodD47_stopD (s := s) ht hEg hp
  have hiff := hSe ⟨stopD47 W VL VR ζ s t p, hgD⟩
  simp only [mem_preimage, imageLineSafe, mem_ofPred_eq, Real.coe_toNNReal _ ht0]
  rw [← hiff]
  change ((t : ℝ) ∈ PcD47 s (stopD47 W VL VR ζ s t p) ∧ _) ↔ _
  rw [mem_PcD47_stopD_iff hp hg (le_refl (t : ℝ))]
  refine and_congr_right fun htP => ?_
  rw [fwdHull_rpath_qW_capClock hEg hp htP, ← fillH_qgCurve_eq hEg hp htP]
  have himg : gammaD47 s (stopD47 W VL VR ζ s t p) '' Icc 0 t =
      qgCurve W s E p '' Icc 0 t :=
    image_congr fun u hu => gammaD47_stopD hp hg hu.2
  rw [himg]

end InteractingSLE.Sec5.CfPhys
