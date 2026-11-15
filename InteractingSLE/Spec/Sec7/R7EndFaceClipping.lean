/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInMixedInf

/-!
# Closed-pocket containment of the certified proper barrier

PROVE-R7-GAPEQ. Retain R.3's disc containment when the opening corner is the flow
seed, so the corresponding physical middle arc is a proper tail to infinity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open QuantumZipper.CA (cayley)
open scoped NNReal

namespace InteractingSLE.Sec7.R7EndFace

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

/-- The clipped middle frontier is a proper reverse-visited barrier wholly in the
closed infinite-end pocket, covering every physical middle-frontier contact there. -/
theorem exists_closed_midBarrierInf {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) {η : ℝ → ℂ}
    (hη0 : η 0 = 0) (hrevM : IsWallReverseVisit M η) :
    ∃ B : ℝ → ℂ, ContinuousOn B (Ici 0) ∧
      Tendsto (fun v => ‖B v‖) atTop atTop ∧
      (∀ v ∈ Ioi (0 : ℝ), B v ∈ H) ∧ B '' Ici 0 ⊆ closure (cfPocket R L r) ∧
      (IsReverseVisitOrderInf B fun t => η '' Icc 0 t) ∧ B 0 = cfArcRInf R L r 0 ∧
      ∀ z ∈ closure (cfPocket R L r), z ∈ H → negInv z ∈ range M → z ∈ B '' Ici 0 := by
  obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, hin, hout⟩ := exists_midTimes h hO hcR hcL
  have hα := hM.isProperArc.isDiscCrosscut_toDisc
  have hσ0 : σM = 0 := hα.inj ⟨h0σ, hστ.le.trans hτ1⟩ ⟨le_rfl, zero_le_one⟩
    (hσa.trans ((h.openPt_eq_neg_one_iff.2 h0).trans hα.zero.symm))
  have hτ0 : 0 < τM := hσ0 ▸ hστ
  obtain ⟨hc, -, ht, himg, hH⟩ := crosscut_arcInf_props hα hτ0 hτ1
  refine ⟨midArcInf M τM, hc, ht, hH, ?_, rev_inf_of_wall hM hη0 hrevM hτ0 hτ1, ?_, ?_⟩
  · change (fun v => cfPt (toDisc (realPath M) (τM / (1 + v)))) '' Ici 0 ⊆ _
    rw [himg]
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hcl := hin v ⟨hσ0 ▸ hv.1.le, hv.2⟩
    have hne := crosscut_ne_neg_one hα ⟨hv.1, hv.2.trans hτ1⟩
    have hm := (continuousAt_cfPt hne).continuousWithinAt.mem_closure_image hcl
    rwa [← image_negInv_eq h.changePocket_subset_H] at hm
  · simp only [midArcInf, add_zero, div_one]
    rw [hτb, IsChangeConfigInc.cfArcRInf_zero]
  · intro z hzc hzH hzM
    obtain ⟨t, ht⟩ := hzM
    have hMH : M t ∈ H := ht ▸ negInv_mem_H hzH
    have ht0 : (0 : ℝ) < t := by
      refine lt_of_le_of_ne t.coe_nonneg fun he => ?_
      have he' : t = 0 := by exact_mod_cast he.symm
      rw [he', hM.2.2.1] at hMH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hMH)
    have hz : z = negInv (M t) := by rw [ht, negInv_negInv]
    have hcl := neg_cayley_mem_closure h.changePocket_subset_H hzc
    rw [hz, cayley_negInv (H_subset_Hbar' hMH) (WangWu.ne_zero_of_mem_H hMH), neg_neg,
      ← toDisc_realPath_discTime] at hcl
    have hmem := hout _ (discTime_mem_Icc t) hcl
    have hpos : 0 < discTime (t : ℝ) := div_pos ht0 (by linarith)
    change z ∈ (fun v => cfPt (toDisc (realPath M) (τM / (1 + v)))) '' Ici 0
    rw [himg]
    refine ⟨_, ⟨_, ⟨hpos, hmem.2⟩, rfl⟩, ?_⟩
    rw [toDisc_realPath_discTime, cfPt_cayley (H_subset_Hbar' hMH) (WangWu.ne_zero_of_mem_H hMH), hz]

end InteractingSLE.Sec7.R7EndFace
