/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GateBridgeProper
import InteractingSLE.Spec.Sec7.R7StopInMixed

/-!
# The proper earlier arm of a pocket through a certified middle frontier

Packet PROVE-R7-AUX41OO (Theorem 1.2's R.7, Aux. lemma 41 for pockets with two outer arms).

PROVE-R7-GAPEQ's driver chain (`R7GateBridge.relLoewner_of_change_gate_faces`) needs a *proper earlier arm*
(`R7GapEqCorner.HasProperEarlierArm`): a simple proper arc in `ℍ` from the target corner `x₀` to `∞`, unvisited before
the target time and meeting the two pocket sides only at `x₀`. GAPEQ builds it from a reverse-visited wall
(`hasProperEarlierArm_of_one_reverse_wall`). For a pocket with two outer arms neither wall is reverse visited.

Here the arm is the **earlier prefix of the certified middle frontier `M`** (`β_R` in R.7), read from its disc time `u`
at `x₀` (Lemma R.3's clipping, `R7StopIn.exists_midTimes`) back to its seed (`∞` in the counterflow chart). It is
unvisited before `σ` by `M`'s reverse visit order (`R7GateBridge.earlier_prefix_unvisited`), and it meets both pocket
sides only at `x₀` by the increasing contact orders of `(R, M)` and `(M, L)` (`IsOrderedArcs`). No reverse visit order
of either wall is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.Aux41OO

open WangWu Lemma71I PocketJordan PocketCoord R7GapEqCorner R7GateBridge R7StopIn

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **The disc time of the opening corner on the middle frontier** (Lemma R.3's clipping): a middle arc between the
walls, with no common arc with either, passes through the opening corner `x₀` at a disc time `u ∈ (0, 1)`. -/
theorem exists_midOpen (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) :
    ∃ u : ℝ, 0 < u ∧ u < 1 ∧ toDisc (realPath M) u = openPt R L r := by
  obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, -, -, -⟩ := exists_midTimes h hO hcR hcL
  have hσpos : 0 < σM := by
    refine lt_of_le_of_ne h0σ fun he => h.openPt_ne_neg_one h0 ?_
    rw [← hσa, ← he]
    exact hM.isProperArc.isDiscCrosscut_toDisc.zero
  exact ⟨σM, hσpos, hστ.trans_le hτ1, hσa⟩

/-- **The proper earlier arm through the certified middle frontier.** For a change pocket between ordered walls with
a simple proper middle arc `M` (no common arc with either wall) visited in reverse order, and a target corner not
visited before `σ`, the earlier prefix of `M` from `x₀` is a proper earlier arm. Neither wall is assumed to be
reverse visited (both may be outer). -/
theorem hasProperEarlierArm_middle (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) {η : ℝ → ℂ} {σ : ℝ} (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit M η) (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) :
    HasProperEarlierArm η (cfArcR R L r) (cfArcL R L r) σ := by
  obtain ⟨u, hu0, hu1, hua⟩ := exists_midOpen h h0 hM hO hcR hcL
  have hαM : IsDiscCrosscut (toDisc (realPath M)) := hM.isProperArc.isDiscCrosscut_toDisc
  obtain ⟨hc, hi, ht, -, -⟩ := crosscut_arcInf_props hαM hu0 hu1.le
  have hx : cfPt (toDisc (realPath M) u) = cfArcR R L r 0 := by
    rw [hua, IsChangeConfigInc.cfArcR_zero]
  obtain ⟨hRlo, hRhi, hRlh, hLlo, hLhi, hLlh, hLa, -⟩ := h.changeCorner_props
  have hincRM := strictMonoOn_contactMap h.isDiscCrosscut_right hαM
    ((disjoint_rightSideOf_iff hO.right hO.middle).1 hO.right_middle)
  have hincML := strictMonoOn_contactMap hαM h.isDiscCrosscut_left
    ((disjoint_rightSideOf_iff hO.middle hO.left).1 hO.middle_left)
  have hu : u ∈ Icc (0 : ℝ) 1 := ⟨hu0.le, hu1.le⟩
  refine ⟨fun v => cfPt (toDisc (realPath M) (u / (1 + v))), hc, hi, ?_, fun v hv => ?_, ht, ?_, ?_, ?_⟩
  · simp only [add_zero, div_one]
    exact hx
  · have hm := div_one_add_mem hu0 hv
    exact cfPt_mem_H (hαM.mem_disc _ ⟨hm.1, hm.2.trans_lt hu1⟩)
  · have hxf' : cfPt (toDisc (realPath M) u) ∉ η '' Ico 0 σ := hx ▸ hxf
    exact earlier_prefix_unvisited hM hu0 hu1.le hη0 hrev hxf'
  · intro v hv w hw he
    have hm := (IsChangeConfigInc.affine_mem hRlh).1 hv
    have hd := div_one_add_mem hu0 hw
    have hRmem : rightLo R L r + v * (rightHi R L r - rightLo R L r) ∈ Ioc (0 : ℝ) 1 :=
      ⟨(h.rightLo_pos h0).trans_le hm.1, hm.2.trans hRhi.2⟩
    have hMmem : u / (1 + w) ∈ Ioc (0 : ℝ) 1 := ⟨hd.1, hd.2.trans hu1.le⟩
    have he' := injOn_cfPt (crosscut_ne_neg_one h.isDiscCrosscut_right hRmem)
      (crosscut_ne_neg_one hαM hMmem) he
    have hcorner : toDisc (realPath R) (rightLo R L r) = toDisc (realPath M) u := hua.symm
    have hlo := contact_eq_of_opposite_parameters hαM hincRM hRlo (Ioc_subset_Icc_self hRmem) hu
      (Ioc_subset_Icc_self hMmem) hcorner he' hm.1 hd.2
    change cfPt (toDisc (realPath R) _) = cfPt (toDisc (realPath R) _)
    rw [← hlo, zero_mul, add_zero]
  · intro v hv w hw he
    have hm := (IsChangeConfigInc.affine_mem hLlh).1 hv
    have hd := div_one_add_mem hu0 hw
    have hLmem : leftLo R L r + v * (leftHi R L r - leftLo R L r) ∈ Ioc (0 : ℝ) 1 :=
      ⟨(h.leftLo_pos h0).trans_le hm.1, hm.2.trans hLhi.2⟩
    have hMmem : u / (1 + w) ∈ Ioc (0 : ℝ) 1 := ⟨hd.1, hd.2.trans hu1.le⟩
    have he' := injOn_cfPt (crosscut_ne_neg_one hαM hMmem)
      (crosscut_ne_neg_one h.isDiscCrosscut_left hLmem) he.symm
    have hcorner : toDisc (realPath M) u = toDisc (realPath L) (leftLo R L r) := hua.trans hLa.symm
    have hut := contact_eq_of_opposite_parameters h.isDiscCrosscut_left hincML
      (Ioc_subset_Icc_self hMmem) hu (Ioc_subset_Icc_self hLmem) hLlo he' hcorner hd.2 hm.1
    calc cfArcL R L r v = cfPt (toDisc (realPath M) (u / (1 + w))) := he
      _ = cfArcR R L r 0 := by rw [hut]; exact hx

end InteractingSLE.Sec7.Aux41OO
