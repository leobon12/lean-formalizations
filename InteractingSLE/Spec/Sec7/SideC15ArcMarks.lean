/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Landings

/-!
# Exact comparisons of source times and counterflow force marks

PROVE-SIDE-COLLAR2. Read the actual Jordan mark as the negative inverse
of the flow boundary value, then use the proved order of the incoming
arcs. These are deterministic facts for a general change pocket.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex
open QuantumZipper.CA (cayley)
open scoped NNReal

namespace InteractingSLE.Sec7.SideC15

open WangWu PocketCoord PocketJordan Aux119Bdry Lemma71I SideAnc

/-- The counterflow value on the left arc is the inverse of its real
flow value, at the original wall point and in the original Jordan chart. -/
theorem left_arc_counterflow_mark {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {ψ : ℂ → ℂ} {c : Chart}
    (hF : IsFlowChart R L r (jordanUnif (openPt R L r) ψ) c)
    {t : ℝ} (ht : t ∈ Ioo (leftLo R L r) (leftHi R L r)) :
    (ψ (cfPt (toDisc (realPath L) t))).re =
      -((jordanUnif (openPt R L r) ψ (toDisc (realPath L) t)).re)⁻¹ := by
  have h := hF.config
  obtain ⟨_, _, _, ha, hb, _, hLa, hLb⟩ := h.changeCorner_props
  have hα := h.isDiscCrosscut_left
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩
  have hp : toDisc (realPath L) t ≠ openPt R L r := by
    intro he
    exact ht.1.ne' (hα.inj ht01 ha (he.trans hLa.symm))
  have hq : toDisc (realPath L) t ≠ closePt R L r := by
    intro he
    exact ht.2.ne (hα.inj ht01 hb (he.trans hLb.symm))
  have hfr : toDisc (realPath L) t ∈ frontier (cayley '' changePocket R L r) := by
    rw [Aux119Bdry.frontier_eq h]
    exact Or.inr ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  exact counterflow_mark_eq_neg_inv hp
    (hF.unif.im_eq_zero (isOpen_cayley h) (closePt_notMem h) hfr hq)

/-- The same exact coordinate identity on the right incoming arc. -/
theorem right_arc_counterflow_mark {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {ψ : ℂ → ℂ} {c : Chart}
    (hF : IsFlowChart R L r (jordanUnif (openPt R L r) ψ) c)
    {t : ℝ} (ht : t ∈ Ioo (rightLo R L r) (rightHi R L r)) :
    (ψ (cfPt (toDisc (realPath R) t))).re =
      -((jordanUnif (openPt R L r) ψ (toDisc (realPath R) t)).re)⁻¹ := by
  have h := hF.config
  obtain ⟨hu, hv, _, _, _, _, _, _⟩ := h.changeCorner_props
  have hα := h.isDiscCrosscut_right
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hu.1.trans ht.1.le, ht.2.le.trans hv.2⟩
  have hp : toDisc (realPath R) t ≠ openPt R L r := by
    intro he
    exact ht.1.ne' (hα.inj ht01 hu he)
  have hq : toDisc (realPath R) t ≠ closePt R L r := by
    intro he
    exact ht.2.ne (hα.inj ht01 hv he)
  have hfr : toDisc (realPath R) t ∈ frontier (cayley '' changePocket R L r) := by
    rw [Aux119Bdry.frontier_eq h]
    exact Or.inl ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  exact counterflow_mark_eq_neg_inv hp
    (hF.unif.im_eq_zero (isOpen_cayley h) (closePt_notMem h) hfr hq)

/-- The left change mark lies before the present counterflow coordinate
exactly when the present own disc time is before the change time. -/
theorem left_mark_le_iff {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {ψ : ℂ → ℂ} {c : Chart}
    (hF : IsFlowChart R L r (jordanUnif (openPt R L r) ψ) c)
    {s t ξ : ℝ} (hs : s ∈ Ioo (leftLo R L r) (leftHi R L r))
    (ht : t ∈ Ioo (leftLo R L r) (leftHi R L r))
    (hξ : jordanUnif (openPt R L r) ψ (toDisc (realPath L) t) = (ξ : ℂ)) :
    (ψ (cfPt (toDisc (realPath L) s))).re ≤ -ξ⁻¹ ↔ t ≤ s := by
  have hn := hF.config.re_neg_left_of_re_pos hF.unif (hF.orient _ hF.unif)
  have htξ : (jordanUnif (openPt R L r) ψ (toDisc (realPath L) t)).re = ξ := by
    rw [hξ, Complex.ofReal_re]
  rw [left_arc_counterflow_mark hF hs, ← htξ,
    neg_inv_le_neg_inv_iff_of_neg (hn s hs) (hn t ht)]
  exact (strictAntiOn_left_flowArc hF).le_iff_ge
    (Ioo_subset_Ico_self hs) (Ioo_subset_Ico_self ht)

/-- On the right side the corresponding strict force-mark comparison
is exactly the strict comparison of the own disc times. -/
theorem right_lt_mark_iff {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {ψ : ℂ → ℂ} {c : Chart}
    (hF : IsFlowChart R L r (jordanUnif (openPt R L r) ψ) c)
    {s t ξ : ℝ} (hs : s ∈ Ioo (rightLo R L r) (rightHi R L r))
    (ht : t ∈ Ioo (rightLo R L r) (rightHi R L r))
    (hξ : jordanUnif (openPt R L r) ψ (toDisc (realPath R) t) = (ξ : ℂ)) :
    -ξ⁻¹ < (ψ (cfPt (toDisc (realPath R) s))).re ↔ t < s := by
  have hp := hF.orient _ hF.unif
  have htξ : (jordanUnif (openPt R L r) ψ (toDisc (realPath R) t)).re = ξ := by
    rw [hξ, Complex.ofReal_re]
  rw [right_arc_counterflow_mark hF hs, ← htξ,
    neg_inv_lt_neg_inv_iff_of_pos (hp t ht) (hp s hs)]
  exact (strictMonoOn_right_flowArc hF).lt_iff_lt
    (Ioo_subset_Ico_self ht) (Ioo_subset_Ico_self hs)

/-- Convert the wall's compactified disc time back to its own time. -/
theorem own_time_lt_iff {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (s : ℝ≥0) :
    (arcTime t).toNNReal < s ↔ t < discTime s := by
  have hat : 0 ≤ arcTime t := arcTime_nonneg ht
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hat]
  have h := (strictMonoOn_arcTime.lt_iff_lt ht (discTime_mem_Ico s.coe_nonneg))
  simpa only [arcTime_discTime s.coe_nonneg] using h

end InteractingSLE.Sec7.SideC15
