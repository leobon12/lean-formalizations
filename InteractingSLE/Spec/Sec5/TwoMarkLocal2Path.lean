/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkRetarget
import InteractingSLE.Spec.Supplement.LP6Retarget
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianStmt

/-!
# First-mark retargeting of a stopped two-mark path

The construction of `RetargetData` below uses the explicit positivity of the
first mark. It therefore applies at index zero and needs only a local path.
The transformed equations then follow from the existing retargeting theorem.
No Brownian property of the transformed noise or terminal trace is asserted.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Local2

open Zhan.Retarget

variable {κ a b r : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {w β : ℝ≥0 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ} {vR : Fin 2 → ℝ≥0 → ℝ}
  {T : ℝ≥0∞}

/-- Below the low-weight threshold the first mark cannot collide alone at
an interior time of a local evolution: its weight would be inadmissible. -/
theorem far_eq_of_first_eq (hκ4 : κ < 4) (hr : r ≤ κ / 2 - 4)
    (hp : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ![r, -r] w vL vR β T)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) (hfirst : vR 0 t = w t) :
    vR 1 t = w t := by
  by_contra hfar
  apply hp.not_threshold ht
  right
  rw [Finset.sum_filter, Fin.sum_univ_two]
  simp only [hfirst, hfar, ite_true, ite_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, add_zero]
  linarith only [hκ4, hr]

/-- Before the outer mark collides, the low-weight inner mark is separated. -/
theorem first_gap_pos_of_far_gap_pos (hκ4 : κ < 4) (hr : r ≤ κ / 2 - 4)
    (hp : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ![r, -r] w vL vR β T)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) (hfar : w t < vR 1 t) :
    w t < vR 0 t := by
  refine lt_of_le_of_ne (hp.w_le_vR ht 0) fun h => ?_
  exact hfar.ne (far_eq_of_first_eq hκ4 hr hp ht h.symm).symm

/-- Retargeting data at the first, strictly positive mark of a local path. -/
theorem retargetData_first (ha : 0 < a) (hab : a < b)
    (hp : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ρR w vL vR β T)
    (hq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → w t < vR 0 t) :
    RetargetData (j := 0) (m := 1) xL ![a, b] w vL vR T := by
  have hsep : SepUpTo w (vR 0) T := fun S hS hST =>
    ⟨hS, continuousOn_real_of_lt hp.continuousOn_w hST,
      continuousOn_real_of_lt (hp.continuousOn_vR 0) hST,
      fun s hs => sub_pos.2 (hq _ (lt_of_mem_Icc hST hs))⟩
  have hcont : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
      ContinuousOn (fun s : ℝ => 2 / (w s.toNNReal - vR 0 s.toNNReal))
        (uIcc 0 (t : ℝ)) := by
    intro t ht
    have hs := hsep t t.coe_nonneg (by simpa only [Real.toNNReal_coe] using ht)
    rw [uIcc_of_le t.coe_nonneg]
    refine continuousOn_const.div (hs.cont_w.sub hs.cont_vk) fun s hs' => ?_
    exact sub_ne_zero.2 (hq _ (lt_of_mem_Icc
      (by simpa only [Real.toNNReal_coe] using ht) hs')).ne
  have hstrict : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → vR 0 t < vR 1 t := by
    intro t ht
    refine lt_of_marks hab (fun t ht => hp.vR_eq ht 1) (fun t ht => hp.vR_eq ht 0)
      (fun t ht => hp.integrable_gapR ht 1) (fun t ht => hp.integrable_gapR ht 0)
      (fun t ht => ((hp.integrable_gapR ht 1).continuousOn_mul (hcont t ht)).congr
        fun s _ => ?_) (hp.volume_collisionR 1) (hp.volume_collisionR 0) ht
    simp only [div_eq_mul_inv, mul_inv]
    ring
  refine ⟨ha, hsep, (fun t ht => hp.vR_eq ht 0), (fun i => i.elim0),
    (fun i => i.elim0), ?_, (fun i => i.elim0), ?_⟩
  · intro l
    fin_cases l
    exact ⟨fun t ht => hp.vR_eq ht 1, hp.continuousOn_vR 1,
      fun t ht => hp.integrable_gapR ht 1, hp.volume_collisionR 1,
      fun t ht => (hstrict t ht).ne'⟩
  · intro l t ht
    fin_cases l
    exact hstrict t ht

/-- The full deterministic target change at index zero for a stopped path. -/
theorem isSLEPathUpTo_first (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hp : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ![r, -r] w vL vR β T)
    (hq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → w t < vR 0 t) :
    Sec2.IsSLEPathUpTo κ ![-1, Sec7.targetChangeReal a b]
      (LP.retargetXR (j := 0) (m := 1) ![a, b]) ![κ - 6, -r]
      (LP.retargetρR (j := 0) (m := 1) ![r, -r])
      (newW (j := 0) (m := 1) ![a, b] w vR)
      (newVL (j := 0) (m := 1) ![a, b] w vL vR)
      (newVR (j := 0) (m := 1) ![a, b] w vR)
      (newB (j := 0) (m := 1) κ xL ![a, b] ρL ![r, -r] w vL vR)
      (newHorizon a w (vR 0) T) := by
  have hd := retargetData_first ha hab hp hq
  have hD := LP.isDistinctForceWord_of_two xL ![a, b] ha.le hab
  have h := isSLEPathUpTo_retarget hp hd hD hκ
  rw [← TwoMark.retargetXL_eq xL a b, ← TwoMark.retargetRhoL_eq ρL κ r]
  exact h

/-- First-mark retargeting before its separation time needs no maximality. -/
theorem isSLEPathUpTo_first_sep (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hp : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ![r, -r] w vL vR β T) :
    Sec2.IsSLEPathUpTo κ ![-1, Sec7.targetChangeReal a b]
      (LP.retargetXR (j := 0) (m := 1) ![a, b]) ![κ - 6, -r]
      (LP.retargetρR (j := 0) (m := 1) ![r, -r])
      (newW (j := 0) (m := 1) ![a, b] w vR)
      (newVL (j := 0) (m := 1) ![a, b] w vL vR)
      (newVR (j := 0) (m := 1) ![a, b] w vR)
      (newB (j := 0) (m := 1) κ xL ![a, b] ρL ![r, -r] w vL vR)
      (newHorizon a w (vR 0) (sepTime w (vR 0) T)) :=
  isSLEPathUpTo_first hκ ha hab (hp.mono (sepTime_le w (vR 0) T))
    fun _ ht => lt_of_lt_sepTime ht

end InteractingSLE.Sec5.TwoMark.Local2
