/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqGeoCollar

/-!
# The actual finite change-pocket outer collars

PROVE-R7-GAPEQ. The collar uses the full selected outer wall's own exterior side. Its
frontier is locally the selected clipped subarc. The certified exterior enters only through
global side inclusion. Thus neither `hinc` nor `hfr` of the previous finite reduction remains.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.R7GapEqGeo

open WangWu Lemma71I PocketJordan PocketCoord R7StopIn R7GapEq R7GapEqFin

/-- A clipped affine parametrization whose image lies on the pocket frontier contains the
whole open clipped disc segment in the closed pocket. -/
theorem cf_clip_subset_closure {α A : ℝ → ℂ} {C : Set ℂ} {a b : ℝ} (hab : a < b)
    (hA : ∀ v ∈ Icc (0 : ℝ) 1, A v = cfPt (α (a + v * (b - a))))
    (hAC : A '' Icc 0 1 ⊆ frontier C) :
    cfPt '' (α '' Ioo a b) ⊆ closure C := by
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
  rw [← image_affine_Icc_zero_one hab.le] at hs'
  obtain ⟨v, hv, rfl⟩ := hs'
  exact frontier_subset_closure (hAC ⟨v, hv, hA v hv⟩)

/-- **Right outer collar for the actual finite change pocket.** `hside` is the global
ordered-side inclusion into the forbidden exterior; the other geometric hypotheses are
the existing change configuration and the pocket's orientation. -/
theorem hasExteriorCollar_cfArcR {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hCl : changePocket R L r ⊆ leftSideOf (range R)) {F K : Set ℂ}
    (hside : negInv '' rightSideOf (range R) ⊆ F)
    (hK : frontier (cfPocket R L r) ⊆ K) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasExteriorCollar (cfPocket R L r) F K (cfArcR R L r v) := by
  have hC := h.isCfPocket h0
  obtain ⟨ha, hb, hab, -⟩ := h.changeCorner_props
  let t := rightLo R L r + v * (rightHi R L r - rightLo R L r)
  have ht : t ∈ Ioo (rightLo R L r) (rightHi R L r) :=
    ⟨lt_add_of_pos_right _ (mul_pos hv.1 (sub_pos.2 hab)),
      ((IsChangeConfigInc.affine_mem hab).2.2 ⟨hv.1.le, hv.2⟩).2⟩
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨(h.rightLo_pos h0).trans ht.1,
    ht.2.trans_le hb.2⟩
  have hα := h.isDiscCrosscut_right
  have hne : toDisc (realPath R) t ≠ -1 := fun he => by
    have heq := hα.inj ⟨ht01.1.le, ht01.2.le⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hα.zero.symm)
    exact ht01.1.ne' heq
  have hpH := hC.mem_H₁ v ⟨hv.1.le, hv.2⟩
  have hclip : cfPt '' (toDisc (realPath R) '' Ioo (rightLo R L r) (rightHi R L r)) ⊆
      closure (cfPocket R L r) := cf_clip_subset_closure hab (fun _ _ => rfl)
        (hC.frontier_eq.symm ▸ subset_union_left)
  have hfr := local_frontier_right_clip h.right ha.1 hb.2 ht
    (show -cayley (cfArcR R L r v) = toDisc (realPath R) t from neg_cayley_cfPt hne) hpH hclip
  obtain ⟨he, -⟩ := cfPt_toDisc_of_mem h.right ht01
  have hpR : negInv (cfArcR R L r v) ∈ range R := by
    change negInv (cfPt (toDisc (realPath R) t)) ∈ range R
    rw [he, negInv_negInv]
    exact mem_range_self _
  have hRR : Disjoint (range R) (rightSideOf (range R)) := Set.disjoint_left.2
    fun z hzR hzS => hzS.1.2 hzR
  have hinc := rightWall_exterior_incidence h.right h.right hCl hRR hpR (negInv_mem_H hpH)
  rw [negInv_negInv] at hinc
  obtain ⟨U, hU, hpU, hcov⟩ := hasExteriorCollar_of_exterior_incidence hC.isOpen hC.isConnected
    hC.isBounded (isJordanCurve_frontier_of_isCfPocket hC)
    (hC.frontier_eq.symm ▸ Or.inl ⟨v, ⟨hv.1.le, hv.2.le⟩, rfl⟩)
    (forbidden_right h.right).1 hK hinc hfr
  refine ⟨U, hU, hpU, fun z hz => ?_⟩
  rcases hcov hz with (hzC | hzF) | hzK
  · exact Or.inl (Or.inl hzC)
  · exact Or.inl (Or.inr (hside hzF))
  · exact Or.inr hzK

/-- **Left outer collar for the actual finite change pocket**, by the same compact-tail
argument on its left full wall. -/
theorem hasExteriorCollar_cfArcL {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hCr : changePocket R L r ⊆ rightSideOf (range L)) {F K : Set ℂ}
    (hside : negInv '' leftSideOf (range L) ⊆ F)
    (hK : frontier (cfPocket R L r) ⊆ K) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasExteriorCollar (cfPocket R L r) F K (cfArcL R L r v) := by
  have hC := h.isCfPocket h0
  obtain ⟨-, -, -, ha, hb, hab, -⟩ := h.changeCorner_props
  let t := leftLo R L r + v * (leftHi R L r - leftLo R L r)
  have ht : t ∈ Ioo (leftLo R L r) (leftHi R L r) :=
    ⟨lt_add_of_pos_right _ (mul_pos hv.1 (sub_pos.2 hab)),
      ((IsChangeConfigInc.affine_mem hab).2.2 ⟨hv.1.le, hv.2⟩).2⟩
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨(h.leftLo_pos h0).trans ht.1, ht.2.trans_le hb.2⟩
  have hα := h.isDiscCrosscut_left
  have hne : toDisc (realPath L) t ≠ -1 := fun he => by
    have heq := hα.inj ⟨ht01.1.le, ht01.2.le⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hα.zero.symm)
    exact ht01.1.ne' heq
  have hpH := hC.mem_H₂ v ⟨hv.1.le, hv.2⟩
  have hclip : cfPt '' (toDisc (realPath L) '' Ioo (leftLo R L r) (leftHi R L r)) ⊆
      closure (cfPocket R L r) := cf_clip_subset_closure hab (fun _ _ => rfl)
        (hC.frontier_eq.symm ▸ subset_union_right)
  have hfr := local_frontier_left_clip h.left ha.1 hb.2 ht
    (show -cayley (cfArcL R L r v) = toDisc (realPath L) t from neg_cayley_cfPt hne) hpH hclip
  obtain ⟨he, -⟩ := cfPt_toDisc_of_mem h.left ht01
  have hpL : negInv (cfArcL R L r v) ∈ range L := by
    change negInv (cfPt (toDisc (realPath L) t)) ∈ range L
    rw [he, negInv_negInv]
    exact mem_range_self _
  have hLL : Disjoint (range L) (rightSideOf (range L)) := Set.disjoint_left.2
    fun z hzL hzS => hzS.1.2 hzL
  have hinc := leftWall_exterior_incidence h.left h.left hCr hLL hpL (negInv_mem_H hpH)
  rw [negInv_negInv] at hinc
  obtain ⟨U, hU, hpU, hcov⟩ := hasExteriorCollar_of_exterior_incidence hC.isOpen hC.isConnected
    hC.isBounded (isJordanCurve_frontier_of_isCfPocket hC)
    (hC.frontier_eq.symm ▸ Or.inr ⟨v, ⟨hv.1.le, hv.2.le⟩, rfl⟩)
    (forbidden_left h.left).1 hK hinc hfr
  refine ⟨U, hU, hpU, fun z hz => ?_⟩
  rcases hcov hz with (hzC | hzF) | hzK
  · exact Or.inl (Or.inl hzC)
  · exact Or.inl (Or.inr (hside hzF))
  · exact Or.inr hzK

end InteractingSLE.Sec7.R7GapEqGeo
