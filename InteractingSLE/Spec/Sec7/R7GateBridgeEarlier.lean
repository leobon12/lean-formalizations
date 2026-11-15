/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqCornerAccess
import InteractingSLE.Spec.Sec7.PocketReverseFields

/-!
# The actual earlier incoming paths of a finite change pocket

PROVE-R7-GAPEQ continuation. Reuse `cfBeta` and the proper-crosscut parametrization.
Increasing common-contact order proves that either earlier prefix meets each selected
pocket side only at the opening corner. No visit order of an outer wall is used here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.R7GateBridge

open WangWu Lemma71I PocketJordan PocketCoord

/-- Oppositely ordered contacts of two crosscuts coincide. This is a specialization of the
existing contact map's strict monotonicity, including contacts at the ends of a pocket. -/
theorem contact_eq_of_opposite_parameters {α β : ℝ → ℂ} (hβ : IsDiscCrosscut β)
    (hinc : StrictMonoOn (contactMap α β) (pocketContactSet α β))
    {s u t v : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (he : α s = β t) (he₀ : α u = β v) (hsu : s ≤ u) (hvt : v ≤ t) : s = u := by
  apply le_antisymm hsu
  apply (hinc.le_iff_le ⟨hu, v, hv, he₀.symm⟩ ⟨hs, t, ht, he.symm⟩).1
  rwa [contactMap_eq hβ hv he₀, contactMap_eq hβ ht he]

/-- Inversion remains injective along the compactified crosscut away from its seed. -/
theorem cfPt_crosscut_inj {α : ℝ → ℂ} (hα : IsDiscCrosscut α) {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1)
    (he : cfPt (α s) = cfPt (α t)) : s = t :=
  hα.inj (Ioc_subset_Icc_self hs) (Ioc_subset_Icc_self ht)
    (injOn_cfPt (crosscut_ne_neg_one hα hs) (crosscut_ne_neg_one hα ht) he)

/-- The left-wall counterpart of the already landed `cfBeta`. -/
def cfEarlierL (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (v : ℝ) : ℂ :=
  cfPt (toDisc (realPath L) (leftLo R L r / (1 + v)))

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- The left earlier prefix is simple and proper in `H`, starting at the opening corner. -/
theorem cfEarlierL_props (h : IsChangeConfigInc R L r)
    (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    ContinuousOn (cfEarlierL R L r) (Ici 0) ∧ InjOn (cfEarlierL R L r) (Ici 0) ∧
      cfEarlierL R L r 0 = cfArcR R L r 0 ∧
      Tendsto (fun v => ‖cfEarlierL R L r v‖) atTop atTop ∧
      ∀ v ∈ Ici (0 : ℝ), cfEarlierL R L r v ∈ H := by
  obtain ⟨-, -, -, -, hb, hab, -⟩ := h.changeCorner_props
  have ha0 := h.leftLo_pos h0
  have ha1 : leftLo R L r < 1 := hab.trans_le hb.2
  obtain ⟨hc, hi, ht, -, -⟩ := crosscut_arcInf_props h.isDiscCrosscut_left ha0 ha1.le
  refine ⟨hc, hi, ?_, ht, fun v hv => ?_⟩
  · change cfPt (toDisc (realPath L) (leftLo R L r / (1 + 0))) = cfArcR R L r 0
    rw [add_zero, div_one, ← (h.isCfPocket h0).junction]
    simp only [cfArcL, zero_mul, add_zero]
  · have hm := div_one_add_mem ha0 hv
    exact cfPt_mem_H (h.isDiscCrosscut_left.mem_disc _ ⟨hm.1, hm.2.trans_lt ha1⟩)

/-- The right pocket side and its earlier right prefix meet only at the target. -/
theorem cfArcR_inter_cfBeta (h : IsChangeConfigInc R L r)
    (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hw : w ∈ Ici (0 : ℝ))
    (he : cfArcR R L r v = cfBeta R L r w) : cfArcR R L r v = cfArcR R L r 0 := by
  obtain ⟨hu, hh, huh, -⟩ := h.changeCorner_props
  have hm := (IsChangeConfigInc.affine_mem huh).1 hv
  have hb := div_one_add_mem (h.rightLo_pos h0) hw
  have hp := cfPt_crosscut_inj h.isDiscCrosscut_right
    ⟨(h.rightLo_pos h0).trans_le hm.1, hm.2.trans hh.2⟩
    ⟨hb.1, hb.2.trans (huh.le.trans hh.2)⟩ he
  have ht : rightLo R L r + v * (rightHi R L r - rightLo R L r) = rightLo R L r :=
    le_antisymm (hp ▸ hb.2) hm.1
  change cfPt (toDisc (realPath R) _) = cfPt (toDisc (realPath R) _)
  rw [ht, zero_mul, add_zero]

/-- Increasing contact order excludes a later left-side point from the earlier right prefix. -/
theorem cfArcL_inter_cfBeta (h : IsChangeConfigInc R L r)
    (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hw : w ∈ Ici (0 : ℝ))
    (he : cfArcL R L r v = cfBeta R L r w) : cfArcL R L r v = cfArcR R L r 0 := by
  obtain ⟨hu, hh, huh, ha, hb, hab, hLa, -⟩ := h.changeCorner_props
  have hm := (IsChangeConfigInc.affine_mem hab).1 hv
  have hd := div_one_add_mem (h.rightLo_pos h0) hw
  have hRmem : rightLo R L r / (1 + w) ∈ Ioc (0 : ℝ) 1 :=
    ⟨hd.1, hd.2.trans (huh.le.trans hh.2)⟩
  have hLmem : leftLo R L r + v * (leftHi R L r - leftLo R L r) ∈ Ioc (0 : ℝ) 1 :=
    ⟨(h.leftLo_pos h0).trans_le hm.1, hm.2.trans hb.2⟩
  have he' := (injOn_cfPt (crosscut_ne_neg_one h.isDiscCrosscut_left hLmem)
    (crosscut_ne_neg_one h.isDiscCrosscut_right hRmem) he).symm
  have hdlo := contact_eq_of_opposite_parameters h.isDiscCrosscut_left h.inc
    (Ioc_subset_Icc_self hRmem) hu (Ioc_subset_Icc_self hLmem) ha he' hLa.symm hd.2 hm.1
  calc
    cfArcL R L r v = cfBeta R L r w := he
    _ = cfArcR R L r 0 := by simp only [cfBeta, cfArcR, hdlo, zero_mul, add_zero]

/-- The left pocket side and its earlier left prefix meet only at the target. -/
theorem cfArcL_inter_cfEarlierL (h : IsChangeConfigInc R L r)
    (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hw : w ∈ Ici (0 : ℝ))
    (he : cfArcL R L r v = cfEarlierL R L r w) : cfArcL R L r v = cfArcR R L r 0 := by
  obtain ⟨-, -, -, ha, hb, hab, -⟩ := h.changeCorner_props
  have hm := (IsChangeConfigInc.affine_mem hab).1 hv
  have hd := div_one_add_mem (h.leftLo_pos h0) hw
  have hp := cfPt_crosscut_inj h.isDiscCrosscut_left
    ⟨(h.leftLo_pos h0).trans_le hm.1, hm.2.trans hb.2⟩
    ⟨hd.1, hd.2.trans (hab.le.trans hb.2)⟩ he
  have ht : leftLo R L r + v * (leftHi R L r - leftLo R L r) = leftLo R L r :=
    le_antisymm (hp ▸ hd.2) hm.1
  rw [← (h.isCfPocket h0).junction]
  change cfPt (toDisc (realPath L) _) = cfPt (toDisc (realPath L) _)
  rw [ht, zero_mul, add_zero]

/-- Increasing contact order also excludes a later right-side point from the earlier left prefix. -/
theorem cfArcR_inter_cfEarlierL (h : IsChangeConfigInc R L r)
    (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hw : w ∈ Ici (0 : ℝ))
    (he : cfArcR R L r v = cfEarlierL R L r w) : cfArcR R L r v = cfArcR R L r 0 := by
  obtain ⟨hu, hh, huh, ha, hb, hab, hLa, -⟩ := h.changeCorner_props
  have hm := (IsChangeConfigInc.affine_mem huh).1 hv
  have hd := div_one_add_mem (h.leftLo_pos h0) hw
  have hRmem : rightLo R L r + v * (rightHi R L r - rightLo R L r) ∈ Ioc (0 : ℝ) 1 :=
    ⟨(h.rightLo_pos h0).trans_le hm.1, hm.2.trans hh.2⟩
  have hLmem : leftLo R L r / (1 + w) ∈ Ioc (0 : ℝ) 1 :=
    ⟨hd.1, hd.2.trans (hab.le.trans hb.2)⟩
  have he' := injOn_cfPt (crosscut_ne_neg_one h.isDiscCrosscut_right hRmem)
    (crosscut_ne_neg_one h.isDiscCrosscut_left hLmem) he
  have ht := contact_eq_of_opposite_parameters h.isDiscCrosscut_left h.inc hu
    (Ioc_subset_Icc_self hRmem) ha (Ioc_subset_Icc_self hLmem) hLa.symm he' hm.1 hd.2
  change cfPt (toDisc (realPath R) _) = cfPt (toDisc (realPath R) _)
  rw [← ht, zero_mul, add_zero]

end InteractingSLE.Sec7.R7GateBridge
