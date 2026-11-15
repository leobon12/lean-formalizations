/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInMixed

/-!
# Retaining closed-pocket containment in the certified frontier clipping

PROVE-R7-GAPEQ. The landed disc-time clipping already proves containment. This adapter
keeps that conclusion when passing to the counterflow chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open QuantumZipper.CA (cayley)
open scoped NNReal

namespace InteractingSLE.Sec7.R7Survive

open WangWu Lemma71I PocketCoord PocketJordan R7StopIn

/-- The full clipped middle arc lies in the closed physical pocket. -/
theorem midArc_subset_closure {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {σM τM : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hστ : σM < τM)
    (hin : ∀ t ∈ Icc σM τM, toDisc (realPath M) t ∈ closure (cayley '' changePocket R L r)) :
    midArc M σM τM '' Icc 0 1 ⊆ closure (cfPocket R L r) := by
  rw [midArc_image hστ]
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  have hcl := hin t ht
  have hne : toDisc (realPath M) t ≠ -1 := fun he =>
    h.neg_one_notMem_closure_cayley h0 (he ▸ hcl)
  have hm := (continuousAt_cfPt hne).continuousWithinAt.mem_closure_image hcl
  rwa [← image_negInv_eq h.changePocket_subset_H] at hm

/-- The middle frontier supplies a continuous reverse-visited barrier, in the closed
pocket, with the same target and entrance as the original walls. -/
theorem exists_closed_midBarrier {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) {η : ℝ → ℂ}
    (hη0 : η 0 = 0) (hrevM : IsWallReverseVisit M η) :
    ∃ B : ℝ → ℂ, ContinuousOn B (Icc 0 1) ∧
      (∀ v ∈ Ico (0 : ℝ) 1, B v ∈ H) ∧ B '' Icc 0 1 ⊆ closure (cfPocket R L r) ∧
      (R16.IsReverseVisitOrder B fun t => η '' Icc 0 t) ∧
      B 0 = cfArcR R L r 0 ∧ B 1 = cfArcR R L r 1 ∧
      ∀ z ∈ closure (cfPocket R L r), z ∈ H → negInv z ∈ range M → z ∈ B '' Icc 0 1 := by
  obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, hin, hout⟩ := exists_midTimes h hO hcR hcL
  have hσpos : 0 < σM := by
    refine lt_of_le_of_ne h0σ fun he => h.openPt_ne_neg_one h0 ?_
    rw [← hσa, ← he]
    exact hM.isProperArc.isDiscCrosscut_toDisc.zero
  refine ⟨midArc M σM τM, (midArc_props hM hσpos hστ hτ1).1, ?_,
    midArc_subset_closure h h0 hστ hin, midArc_rev hM hη0 hrevM hσpos hστ hτ1, ?_, ?_,
    fun z hzc hzH hzM => mem_midArc_of_mem_closure h hM hστ hout hzc hzH hzM⟩
  · intro v hv
    have hm := (PocketCoord.IsChangeConfigInc.affine_mem hστ).1 ⟨hv.1, hv.2.le⟩
    have hlt : σM + v * (τM - σM) < τM := by
      nlinarith [mul_pos (sub_pos.2 hv.2) (sub_pos.2 hστ)]
    exact cfPt_mem_H (hM.isProperArc.isDiscCrosscut_toDisc.mem_disc _
      ⟨hσpos.trans_le hm.1, hlt.trans_le hτ1⟩)
  · rw [midArc_zero, hσa, PocketCoord.IsChangeConfigInc.cfArcR_zero]
  · rw [midArc_one, hτb, PocketCoord.IsChangeConfigInc.cfArcR_one]

end InteractingSLE.Sec7.R7Survive
