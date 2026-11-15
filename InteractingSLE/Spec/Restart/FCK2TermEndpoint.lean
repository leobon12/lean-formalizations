/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2TermHeights

/-! # A geometric threshold has a bad physical incident height -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData FlowStopIdentLL MartChar.RealFlow

/-- A threshold of the original geometric force word occurs at a real
physical endpoint, with the bad incident height on its original seed side.
The datum may jump at the endpoint. -/
theorem bad_incident_of_threshold_geometric_seed {κ θ x : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {w : ℝ≥0 → ℝ} {U : ℝ≥0∞} {η : ℝ≥0 → ℂ} {T : ℝ≥0} {D : ℝ → ℝ}
    (hg : IsGeneratingTrace w U (fun t => η t - x)) (hT : 0 < T)
    (hTU : (T : ℝ≥0∞) ≤ U) (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w s)
    (hthr : ForceWord.ThresholdCondition (flowLineRhoL κ b J x θ) (flowLineRhoR κ b J x θ)
      (D T) (fun i => -rightImg (fun s => -D s) (-flowLineXL b J x i) T)
        (fun j => rightImg D (flowLineXR b J x j) T)) :
    (η T).im = 0 ∧
      (((η T).re ≤ x ∧ sleLambda κ ≤ leftLim b (η T).re + θ * chiC κ) ∨
        (x ≤ (η T).re ∧ rightLim b (η T).re + θ * chiC κ ≤ -sleLambda κ)) := by
  classical
  obtain ⟨hB, hp⟩ := terminal_boundary_data hg hT hTU hD hD0 hDw
  have hD0L : (fun s => -D s) 0 = 0 := by simp only [hD0, neg_zero]
  obtain ⟨hBL, hpL⟩ := terminal_boundary_data (LP.isGeneratingTrace_reflect hg) hT hTU
    hD.neg hD0L (fun s hs => congrArg Neg.neg (hDw s hs))
  rcases hthr with hl | hr
  · have hne : (univ.filter (fun i =>
        -rightImg (fun s => -D s) (-flowLineXL b J x i) T = D T)).Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty.1 hn, sum_empty] at hl
      norm_num at hl
    obtain ⟨i, hi⟩ := hne
    have hc := neg_eq_iff_eq_neg.1 (mem_filter.1 hi).2
    have hz : rightImg (fun s => -D s) 0 T = -D T :=
      le_antisymm ((rightImg_mono_index hD.neg T.coe_nonneg
        (neg_nonneg.2 (flowLineXL_nonpos_seed b J x i))).trans hc.le)
        (le_rightImg hD.neg 0 T.coe_nonneg)
    have hreal := real_tip_of_rightImg_eq hD.neg hD0L T.coe_nonneg hBL hpL hz
    have him : (η T).im = 0 := by
      simpa only [LP.reflectC, Complex.neg_im, Complex.conj_im, neg_neg,
        Complex.sub_im, Complex.ofReal_im, sub_zero] using hreal.1
    have hx : (η T).re ≤ x := by
      have := hreal.2
      simp only [LP.reflectC, Complex.neg_re, Complex.conj_re, Complex.sub_re,
        Complex.ofReal_re] at this
      linarith only [this]
    have hs := sum_collisionL_eq_leftLim_seed (θ := θ) hκ hb hx
      (vL := fun i => -rightImg (fun s => -D s) (-flowLineXL b J x i) T) (w := D T)
      (fun i => by
        rw [neg_eq_iff_eq_neg]
        simpa only [LP.reflectC, Complex.neg_re, Complex.conj_re, Complex.sub_re,
          Complex.ofReal_re, neg_le_neg_iff, Pi.neg_apply] using
          rightImg_eq_iff_of_zero_collision (D := fun s => -D s)
            hD.neg hD0L T.coe_nonneg hBL hpL hz
            (-flowLineXL b J x i))
    rw [hs] at hl
    exact ⟨him, Or.inl ⟨hx, not_lt.1 (fun h =>
      (not_le_of_gt ((cumWeightLeft_gt_iff hκ).2 h)) hl)⟩⟩
  · have hne : (univ.filter (fun i => rightImg D (flowLineXR b J x i) T = D T)).Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty.1 hn, sum_empty] at hr
      norm_num at hr
    obtain ⟨i, hi⟩ := hne
    have hc := (mem_filter.1 hi).2
    have hz : rightImg D 0 T = D T :=
      le_antisymm ((rightImg_mono_index hD T.coe_nonneg
        (flowLineXR_nonneg_seed b J x i)).trans hc.le) (le_rightImg hD 0 T.coe_nonneg)
    have hreal := real_tip_of_rightImg_eq hD hD0 T.coe_nonneg hB hp hz
    have him : (η T).im = 0 := by simpa using hreal.1
    have hx : x ≤ (η T).re := by
      have := hreal.2
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      linarith only [this]
    have hs := sum_collisionR_eq_rightLim_seed (θ := θ) hκ hb hx
      (vR := fun j => rightImg D (flowLineXR b J x j) T) (w := D T)
      (fun j => by simpa only [Complex.sub_re, Complex.ofReal_re] using
        rightImg_eq_iff_of_zero_collision hD hD0 T.coe_nonneg hB hp hz (flowLineXR b J x j))
    rw [hs] at hr
    exact ⟨him, Or.inr ⟨hx, not_lt.1 (fun h =>
      (not_le_of_gt ((cumWeightRight_gt_iff hκ).2 h)) hr)⟩⟩

end InteractingSLE.Restart.FCPlumb
