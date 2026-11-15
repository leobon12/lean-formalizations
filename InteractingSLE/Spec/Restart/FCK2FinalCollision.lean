/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2Bdry

/-!
# Collision sums at real tips, including boundary jumps

The terminal inverse-map tools identify nonempty collision groups with closed
intervals ending at the real tip. Here their sums are read as the appropriate
one-sided boundary height, including at jumps and at zero.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData FlowStopIdentLL MartChar.RealFlow Sec7.PocketTraversal

/-- A closed left collision prefix reads the left incident height, also at a jump. -/
theorem sum_collisionL_eq_leftLim {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {y w : ℝ} (hy : y ≤ 0) {vL : Fin (flowLineNL b J 0) → ℝ}
    (hc : ∀ i, vL i = w ↔ y ≤ flowLineXL b J 0 i) :
    (∑ i ∈ univ.filter (fun i => vL i = w), flowLineRhoL κ b J 0 θ i) =
      Sec4.cumWeightLeft κ (leftLim b y + θ * chiC κ) := by
  classical
  obtain ⟨a, -, hay, haF, hcut⟩ := exists_left_cut isOpen_univ (mem_univ y) (insert 0 J)
  have haJ : a ∉ J := fun ha => haF (mem_insert_of_mem ha)
  have he : leftLim b y = b a := by
    apply Sec4.leftLim_eq_of_forall hay
    intro z hz
    apply Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb hz.1.le
    intro v hv hvJ
    by_cases hva : v = a
    · exact haJ (hva ▸ hvJ)
    · have hav : a < v := lt_of_le_of_ne hv.1 (Ne.symm hva)
      exact (not_le_of_gt (hv.2.trans_lt hz.2)) ((hcut v (mem_insert_of_mem hvJ)).1 hav)
  rw [sum_collisionL_eq_height hκ hb (hay.trans_le hy) haJ]
  · rw [he]
    rfl
  · intro i
    rw [hc i, sub_zero]
    have hi : flowLineXL b J 0 i ∈ insert 0 J := by
      simpa only [zero_add] using physical_flowLineXL_mem b J 0 i
    exact (hcut _ hi).symm

/-- A closed right collision prefix reads the right incident height, also at a jump. -/
theorem sum_collisionR_eq_rightLim {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {y w : ℝ} (hy : 0 ≤ y) {vR : Fin (flowLineNR b J 0) → ℝ}
    (hc : ∀ i, vR i = w ↔ flowLineXR b J 0 i ≤ y) :
    (∑ i ∈ univ.filter (fun i => vR i = w), flowLineRhoR κ b J 0 θ i) =
      Sec4.cumWeightRight κ (rightLim b y + θ * chiC κ) := by
  classical
  obtain ⟨a, -, hya, haF, hcut⟩ := exists_right_cut isOpen_univ (mem_univ y) (insert 0 J)
  have haJ : a ∉ J := fun ha => haF (mem_insert_of_mem ha)
  have he : rightLim b y = b a := by
    apply Sec4.rightLim_eq_of_forall hya
    intro z hz
    symm
    apply Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb hz.2.le
    intro v hv hvJ
    exact (not_le_of_gt (hz.1.trans_le hv.1)) ((hcut v (mem_insert_of_mem hvJ)).1 hv.2)
  rw [sum_collisionR_eq_height hκ hb (hy.trans_lt hya) haJ]
  · rw [he]
    rfl
  · intro i
    rw [hc i, sub_zero]
    have hi : flowLineXR b J 0 i ∈ insert 0 J := by
      simpa only [zero_add] using physical_flowLineXR_mem b J 0 i
    exact (hcut _ hi).symm

section Images
variable {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {W : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {t : ℝ≥0}

/-- Every right collision sum is zero or reads the real tip's right limit. -/
theorem sum_geomR_zero_or_rightLim (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hc : Continuous W) (h0 : W 0 = 0) (hg : IsGeneratingTrace W U γ)
    (ht : 0 < t) (htU : (t : ℝ≥0∞) ≤ U) :
    (∑ i ∈ univ.filter (fun i => rightImg (fun s : ℝ => W s.toNNReal)
        (flowLineXR b J 0 i) t = W t), flowLineRhoR κ b J 0 θ i) = 0 ∨
      ((γ t).im = 0 ∧ 0 ≤ (γ t).re ∧
        (∑ i ∈ univ.filter (fun i => rightImg (fun s : ℝ => W s.toNNReal)
          (flowLineXR b J 0 i) t = W t), flowLineRhoR κ b J 0 θ i) =
          Sec4.cumWeightRight κ (rightLim b (γ t).re + θ * chiC κ)) := by
  classical
  let D : ℝ → ℝ := fun s => W s.toNNReal
  have hD : Continuous D := hc.comp continuous_real_toNNReal
  have hD0 : D 0 = 0 := by simpa only [D, Real.toNNReal_zero] using h0
  obtain ⟨hB, hp⟩ := terminal_boundary_data hg ht htU hD hD0
    (fun s _ => by simp only [D, Real.toNNReal_coe])
  by_cases hz : rightImg D 0 t = D t
  · have hr := real_tip_of_rightImg_eq hD hD0 t.coe_nonneg hB hp hz
    refine Or.inr ⟨hr.1, hr.2, ?_⟩
    apply sum_collisionR_eq_rightLim hκ hb hr.2
    intro i
    simpa only [D, Real.toNNReal_coe] using
      rightImg_eq_iff_of_zero_collision hD hD0 t.coe_nonneg hB hp hz (flowLineXR b J 0 i)
  · left
    apply Finset.sum_eq_zero
    intro i hi
    have he := (Finset.mem_filter.1 hi).2
    apply False.elim
    apply hz
    have hm := rightImg_mono_index hD t.coe_nonneg (flowLineXR_nonneg_seed b J 0 i)
    have hw := le_rightImg hD 0 t.coe_nonneg
    simpa only [D, Real.toNNReal_coe] using le_antisymm (hm.trans he.le)
      (show W t ≤ rightImg D 0 t by simpa only [D, Real.toNNReal_coe] using hw)

/-- Every left collision sum is zero or reads the real tip's left limit. -/
theorem sum_geomL_zero_or_leftLim (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hc : Continuous W) (h0 : W 0 = 0) (hg : IsGeneratingTrace W U γ)
    (ht : 0 < t) (htU : (t : ℝ≥0∞) ≤ U) :
    (∑ i ∈ univ.filter (fun i => -rightImg (fun s : ℝ => -W s.toNNReal)
        (-flowLineXL b J 0 i) t = W t), flowLineRhoL κ b J 0 θ i) = 0 ∨
      ((γ t).im = 0 ∧ (γ t).re ≤ 0 ∧
        (∑ i ∈ univ.filter (fun i => -rightImg (fun s : ℝ => -W s.toNNReal)
          (-flowLineXL b J 0 i) t = W t), flowLineRhoL κ b J 0 θ i) =
          Sec4.cumWeightLeft κ (leftLim b (γ t).re + θ * chiC κ)) := by
  classical
  let D : ℝ → ℝ := fun s => -W s.toNNReal
  have hD : Continuous D := (hc.comp continuous_real_toNNReal).neg
  have hD0 : D 0 = 0 := by simp only [D, Real.toNNReal_zero, h0, neg_zero]
  obtain ⟨hB, hp⟩ := terminal_boundary_data (LP.isGeneratingTrace_reflect hg) ht htU hD hD0
    (fun s _ => by simp only [D, Real.toNNReal_coe, Pi.neg_apply])
  by_cases hz : rightImg D 0 t = D t
  · have hr := real_tip_of_rightImg_eq hD hD0 t.coe_nonneg hB hp hz
    have him : (γ t).im = 0 := by simpa only [LP.reflectC, Complex.neg_im,
      Complex.conj_im, neg_neg] using hr.1
    have hre : (γ t).re ≤ 0 := by
      simpa only [LP.reflectC, Complex.neg_re, Complex.conj_re, neg_nonneg] using hr.2
    refine Or.inr ⟨him, hre, ?_⟩
    apply sum_collisionL_eq_leftLim hκ hb hre
    intro i
    rw [neg_eq_iff_eq_neg]
    have he := rightImg_eq_iff_of_zero_collision hD hD0 t.coe_nonneg hB hp hz
      (-flowLineXL b J 0 i)
    simpa only [D, Real.toNNReal_coe, LP.reflectC, Complex.neg_re,
      Complex.conj_re, neg_le_neg_iff] using he
  · left
    apply Finset.sum_eq_zero
    intro i hi
    have he := neg_eq_iff_eq_neg.1 (Finset.mem_filter.1 hi).2
    apply False.elim
    apply hz
    have hm := rightImg_mono_index hD t.coe_nonneg
      (neg_nonneg.2 (flowLineXL_nonpos_seed b J 0 i))
    have hw := le_rightImg hD 0 t.coe_nonneg
    simpa only [D, Real.toNNReal_coe] using le_antisymm (hm.trans he.le)
      (show -W t ≤ rightImg D 0 t by simpa only [D, Real.toNNReal_coe] using hw)

/-- Incident strict inequalities at the real tip exclude the threshold.
This includes jump tips and does not require a force-path evolution. -/
theorem not_threshold_geom_of_incident_bounds
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hc : Continuous W) (h0 : W 0 = 0) (hg : IsGeneratingTrace W U γ)
    (ht : 0 < t) (htU : (t : ℝ≥0∞) ≤ U)
    (hi : (γ t).im = 0 →
      ((γ t).re ≤ 0 → leftLim b (γ t).re + θ * chiC κ < sleLambda κ) ∧
      (0 ≤ (γ t).re → -sleLambda κ < rightLim b (γ t).re + θ * chiC κ)) :
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (W t)
      (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL b J 0 i) t)
      (fun i => rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR b J 0 i) t) := by
  have hL := sum_geomL_zero_or_leftLim (θ := θ) hκ hb hc h0 hg ht htU
  have hR := sum_geomR_zero_or_rightLim (θ := θ) hκ hb hc h0 hg ht htU
  rintro (hbad | hbad)
  · rcases hL with hL | ⟨him, hre, hL⟩
    · rw [hL] at hbad
      norm_num at hbad
    · rw [hL] at hbad
      exact (not_le_of_gt ((cumWeightLeft_gt_iff hκ).2 ((hi him).1 hre))) hbad
  · rcases hR with hR | ⟨him, hre, hR⟩
    · rw [hR] at hbad
      norm_num at hbad
    · rw [hR] at hbad
      exact (not_le_of_gt ((cumWeightRight_gt_iff hκ).2 ((hi him).2 hre))) hbad

end Images

/-- The incident-height test for every fixed-type reading of a boundary word. -/
theorem not_threshold_type_geom_of_incident_bounds {κ θ : ℝ} (hκ : 0 < κ)
    {c : BoundaryWord} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (htype : c ∈ FCDet.typeSet κ θ nL nR ρL ρR)
    {W : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hc : Continuous W) (h0 : W 0 = 0) (hg : IsGeneratingTrace W U γ)
    (ht : 0 < t) (htU : (t : ℝ≥0∞) ≤ U)
    (hi : (γ t).im = 0 →
      ((γ t).re ≤ 0 → leftLim c.fn (γ t).re + θ * chiC κ < sleLambda κ) ∧
      (0 ≤ (γ t).re → -sleLambda κ < rightLim c.fn (γ t).re + θ * chiC κ)) :
    ¬ ForceWord.ThresholdCondition ρL ρR (W t)
      (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-FCDet.typeXL κ θ nL nR ρL ρR c i) t)
      (fun j => rightImg (fun s : ℝ => W s.toNNReal) (FCDet.typeXR κ θ nL nR ρL ρR c j) t) := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := FCDet.isFlowType_of_mem_typeSet htype
  subst nL nR
  change FCDet.typeXL κ θ _ _ ρL ρR c = flowLineXL c.fn c.jumps 0 at hxL
  change FCDet.typeXR κ θ _ _ ρL ρR c = flowLineXR c.fn c.jumps 0 at hxR
  change ρL = flowLineRhoL κ c.fn c.jumps 0 θ at hρL
  change ρR = flowLineRhoR κ c.fn c.jumps 0 θ at hρR
  rw [hxL, hxR, hρL, hρR]
  exact not_threshold_geom_of_incident_bounds hκ c.isPiecewiseConstantBoundaryData hc h0 hg ht htU hi

end InteractingSLE.Restart.FCPlumb
