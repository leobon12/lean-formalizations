/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2Final

/-!
# The exact accessed-side criterion at a finite endpoint

A real tip is insufficient to identify a nonempty collision group. The
criterion below keeps the zero-side image collision and the incident height
together. It includes jumps and the seed itself.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData FlowStopIdentLL MartChar.RealFlow

/-- A bad incident height on an accessed side is exactly a bad force group.
The zero-image conditions specify access; no converse from a real tip alone
is assumed or used. -/
theorem threshold_geom_iff_accessed_incident_height {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {W : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hc : Continuous W) (h0 : W 0 = 0) (hg : IsGeneratingTrace W U γ)
    (ht : 0 < t) (htU : (t : ℝ≥0∞) ≤ U) :
    ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (W t)
      (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL b J 0 i) t)
      (fun j => rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR b J 0 j) t) ↔
    (rightImg (fun s : ℝ => -W s.toNNReal) 0 t = -W t ∧
      sleLambda κ ≤ leftLim b (γ t).re + θ * chiC κ) ∨
    (rightImg (fun s : ℝ => W s.toNNReal) 0 t = W t ∧
      rightLim b (γ t).re + θ * chiC κ ≤ -sleLambda κ) := by
  classical
  let D : ℝ → ℝ := fun s => W s.toNNReal
  let E : ℝ → ℝ := fun s => -W s.toNNReal
  have hD : Continuous D := hc.comp continuous_real_toNNReal
  have hE : Continuous E := (hc.comp continuous_real_toNNReal).neg
  have hD0 : D 0 = 0 := by simpa only [D, Real.toNNReal_zero] using h0
  obtain ⟨hB, hp⟩ := terminal_boundary_data hg ht htU hD hD0
    (fun s _ => by simp only [D, Real.toNNReal_coe])
  obtain ⟨hBL, hpL⟩ := terminal_boundary_data (LP.isGeneratingTrace_reflect hg) ht htU
    hE (by simp only [E, Real.toNNReal_zero, h0, neg_zero])
    (fun s _ => by simp only [E, Real.toNNReal_coe, Pi.neg_apply])
  have hL (hz : rightImg (fun s : ℝ => -W s.toNNReal) 0 t = -W t) :
      (∑ i ∈ univ.filter (fun i =>
        -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL b J 0 i) t = W t),
          flowLineRhoL κ b J 0 θ i) =
        Sec4.cumWeightLeft κ (leftLim b (γ t).re + θ * chiC κ) := by
    have hr := real_tip_of_rightImg_eq hE
      (by simp only [E, Real.toNNReal_zero, h0, neg_zero]) t.coe_nonneg hBL hpL
      (by simpa only [D, E, Real.toNNReal_coe, Pi.neg_apply] using hz)
    apply sum_collisionL_eq_leftLim hκ hb
      (show (γ t).re ≤ 0 by simpa only [LP.reflectC, Complex.neg_re,
        Complex.conj_re, neg_nonneg] using hr.2)
    intro i
    rw [neg_eq_iff_eq_neg]
    simpa only [D, E, Real.toNNReal_coe, LP.reflectC, Complex.neg_re,
      Complex.conj_re, neg_le_neg_iff] using
      rightImg_eq_iff_of_zero_collision hE
        (by simp only [E, Real.toNNReal_zero, h0, neg_zero]) t.coe_nonneg
        hBL hpL (by simpa only [D, E, Real.toNNReal_coe, Pi.neg_apply] using hz)
        (-flowLineXL b J 0 i)
  have hR (hz : rightImg (fun s : ℝ => W s.toNNReal) 0 t = W t) :
      (∑ i ∈ univ.filter (fun i =>
        rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR b J 0 i) t = W t),
          flowLineRhoR κ b J 0 θ i) =
        Sec4.cumWeightRight κ (rightLim b (γ t).re + θ * chiC κ) := by
    have hr := real_tip_of_rightImg_eq hD hD0 t.coe_nonneg hB hp
      (by simpa only [D, E, Real.toNNReal_coe] using hz)
    apply sum_collisionR_eq_rightLim hκ hb hr.2
    intro i
    simpa only [D, E, Real.toNNReal_coe] using
      rightImg_eq_iff_of_zero_collision hD hD0 t.coe_nonneg hB hp
        (by simpa only [D, E, Real.toNNReal_coe] using hz) (flowLineXR b J 0 i)
  constructor
  · rintro (hl | hr)
    · have hz : rightImg (fun s : ℝ => -W s.toNNReal) 0 t = -W t := by
        by_contra hn
        have he : (∑ i ∈ univ.filter (fun i =>
            -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL b J 0 i) t = W t),
              flowLineRhoL κ b J 0 θ i) = 0 := by
          apply sum_eq_zero
          intro i hi
          apply False.elim
          apply hn
          have hm := rightImg_mono_index hE t.coe_nonneg
            (neg_nonneg.2 (flowLineXL_nonpos_seed b J 0 i))
          exact le_antisymm (hm.trans (neg_eq_iff_eq_neg.1 (mem_filter.1 hi).2).le)
            (by simpa only [D, E, Pi.neg_apply, Real.toNNReal_coe] using
              le_rightImg hE 0 t.coe_nonneg)
        rw [he] at hl
        norm_num at hl
      refine Or.inl ⟨hz, ?_⟩
      rw [hL hz] at hl
      exact not_lt.1 (fun h => (not_le_of_gt ((cumWeightLeft_gt_iff hκ).2 h)) hl)
    · have hz : rightImg (fun s : ℝ => W s.toNNReal) 0 t = W t := by
        by_contra hn
        have he : (∑ i ∈ univ.filter (fun i =>
            rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR b J 0 i) t = W t),
              flowLineRhoR κ b J 0 θ i) = 0 := by
          apply sum_eq_zero
          intro i hi
          apply False.elim
          apply hn
          have hm := rightImg_mono_index hD t.coe_nonneg (flowLineXR_nonneg_seed b J 0 i)
          exact le_antisymm (hm.trans (mem_filter.1 hi).2.le)
            (by simpa only [D, E, Real.toNNReal_coe] using le_rightImg hD 0 t.coe_nonneg)
        rw [he] at hr
        norm_num at hr
      refine Or.inr ⟨hz, ?_⟩
      rw [hR hz] at hr
      exact not_lt.1 (fun h => (not_le_of_gt ((cumWeightRight_gt_iff hκ).2 h)) hr)
  · rintro (⟨hz, hh⟩ | ⟨hz, hh⟩)
    · left
      rw [hL hz]
      exact le_of_not_gt (fun h => (not_lt_of_ge hh) ((cumWeightLeft_gt_iff hκ).1 h))
    · right
      rw [hR hz]
      exact le_of_not_gt (fun h => (not_lt_of_ge hh) ((cumWeightRight_gt_iff hκ).1 h))

end InteractingSLE.Restart.FCPlumb
