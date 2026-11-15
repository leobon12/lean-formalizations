/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux119Lift
import InteractingSLE.Spec.Sec7.PocketMarks

/-!
# Aux. lemma 119 for Aux. lemma 130's change pocket: the flow chart is a two-arc frame

Packet PROVE-STRIPSYS22. Specification §7.4, Aux. lemma 119 and its proof (`source/spec/p385-432.md` L3–L54,
pp. 385–387):

> Let `C` be the Jordan pocket between two consecutive common contacts `x₀, y₀`, with `α_R` on its right and `α_L` on
> its left, both oriented from `x₀` to `y₀`. […] There is a measurably selected derivative-logarithm lift for a
> conformal chart `φ : C → ℍ` taking `x₀` to zero and `y₀` to infinity […] The left incoming arc maps to `ℝ₋` and the
> right one to `ℝ₊`. […] Its restriction to `C` extends as a Jordan boundary embedding by Aux. lemma 30. […] The
> remaining right arc maps to a simple crosscut […] Keep the left prefix through `y₀` and the right prefix through a
> point `p` strictly between `x₀` and `y₀` on its selected arc. Let `D_p` be the unbounded component after these two
> prefixes are removed and filled. Then `C ⊂ D_p`. […] That continuation avoids both retained prefixes, by simplicity
> and common-contact order, and goes to the original target at infinity.

The pocket is the change pocket `changePocket R L r` of Aux. lemma 130 (PROVE-STRIPSYS8): the right wall `R` (the
first incoming path) and the left wall `L`, simple proper curves of `ℍ` from `0` to `∞` in **increasing contact order
only** (`IsChangeConfigInc`; they may cross after the pocket). The flow chart `φ = Ψ ∘ cayley` is given by a two-point
uniformizer `Ψ` of the Cayley image with its Jordan boundary extension (`IsBdryUniformizer`: Aux. lemma 30 for a Jordan
domain, PROVE-STRIPSYS17), oriented (`IsFlowChartOriented`: the open right-wall arc goes to `ℝ₊`, PROVE-STRIPSYS17/18).

This file proves that the flow chart is a two-arc frame (`Aux119Lift.IsTwoArcFrame`), so the common lift of
`Aux119Lift.IsTwoArcFrame.exists_isPocketBranch` applies:

* the chart inverse lands at every point of `ℍ̄` (`Lemma71M.tendsto_inv_of_ext`; the only boundary point at `∞` is the
  closing contact, `one_notMem`), injectively along `ℝ`;
* the landing point of `0` is the opening contact `x₀ = L(s_a) = R(t_a)`; negative points land on the open left arc,
  off `R`, and positive points on the open right arc, off `L` (`land_neg_mem`, `land_pos_mem`: the frontier is the two
  closed arcs; the corners have values `0` and `∞`; the orientation and `re_neg_left_of_re_pos` sort the open arcs);
* **`C ⊂ D_p`** for the corner prefixes through the midpoints of the two selected arcs (`subset_H_diff_fillH_corner`):
  the pocket escapes through a point of the open right arc along the right wall's continuation, which avoids the left
  prefix by the increasing contact order (`tail_notMem_left`: a later contact of `R` with an earlier point of `L`
  contradicts strict monotonicity of the contact map) — "by simplicity and common-contact order".

## Main results

* **`isTwoArcFrame`**: the flow chart of the change pocket is a two-arc frame;
* **`exists_isPocketBranch`**: Aux. lemma 119's common lift for the change pocket (one integer `n` for both selected
  sides, every own prefix, including all angle-change points on the open arcs), and `existsUnique_isPocketBranch`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal

namespace InteractingSLE.Sec7.Aux119Bdry

open WangWu PocketCoord Lemma71I PocketJordan PocketMarks
open Lemma71O (land)
open Aux119Lift (IsTwoArcFrame)

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ}

/-! ### Wall points in the disc -/

section Disc

/-- A wall point of disc time `s < 1`, read back in `ℍ`. -/
theorem cayleyInv_toDisc {η : ℝ≥0 → ℂ} (hη : IsSimpleProper η) {s : ℝ} (hs : s < 1) :
    cayleyInv (toDisc (realPath η) s) = η (arcTime s).toNNReal := by
  rw [toDisc_of_lt hs]
  exact cayleyInv_cayley_of_mem_Hbar (hη.isProperCurve.2.2.1 _)

theorem toDisc_eq_cayley {η : ℝ≥0 → ℂ} {s : ℝ} (hs : s < 1) :
    toDisc (realPath η) s = cayley (η (arcTime s).toNNReal) :=
  toDisc_of_lt hs

/-- The frontier of the Cayley image is the two closed selected arcs. -/
theorem frontier_eq (h : IsChangeConfigInc R L r) :
    frontier (cayley '' changePocket R L r) =
      toDisc (realPath R) '' Icc (rightLo R L r) (rightHi R L r) ∪
        toDisc (realPath L) '' Icc (leftLo R L r) (leftHi R L r) := by
  obtain ⟨-, hj1, hj2, -⟩ := h.changeCorners
  rw [h.cayleyChange_props.2.2, pocketCurve, hj1, hj2]

theorem isOpen_cayley (h : IsChangeConfigInc R L r) : IsOpen (cayley '' changePocket R L r) :=
  Lemma71F.isOpen_cayley_image h.isOpen_changePocket h.changePocket_subset_H

theorem closePt_notMem (h : IsChangeConfigInc R L r) : closePt R L r ∉ cayley '' changePocket R L r := by
  have := h.closePt_mem_frontier
  rw [(isOpen_cayley h).frontier_eq] at this
  exact this.2

/-- **The only boundary point at infinity is the closing contact.** -/
theorem one_notMem (h : IsChangeConfigInc R L r) :
    (1 : ℂ) ∉ closure (cayley '' changePocket R L r) \ {closePt R L r} := by
  rintro ⟨h1c, h1q⟩
  obtain ⟨hu, hv, huv, ha, hb, -, -, hLb⟩ := h.changeCorner_props
  have hαR := h.isDiscCrosscut_right
  have hαL := h.isDiscCrosscut_left
  have h1D : (1 : ℂ) ∉ cayley '' changePocket R L r := fun h1 => by
    have := h.cayleyChange_props.2.1 h1
    rw [mem_ball, dist_zero_right, norm_one] at this
    exact lt_irrefl _ this
  have hfr : (1 : ℂ) ∈ frontier (cayley '' changePocket R L r) := by
    rw [(isOpen_cayley h).frontier_eq]; exact ⟨h1c, h1D⟩
  rw [frontier_eq h] at hfr
  rcases hfr with ⟨s, hs, hs1⟩ | ⟨t, ht, ht1⟩
  · have hs1' : s = 1 := hαR.inj ⟨hu.1.trans hs.1, hs.2.trans hv.2⟩ ⟨zero_le_one, le_rfl⟩ (hs1.trans hαR.one.symm)
    have hv1 : rightHi R L r = 1 := le_antisymm hv.2 (hs1' ▸ hs.2)
    exact h1q (by rw [mem_singleton_iff, closePt, hv1, hαR.one])
  · have ht1' : t = 1 := hαL.inj ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩ ⟨zero_le_one, le_rfl⟩ (ht1.trans hαL.one.symm)
    have hb1 : leftHi R L r = 1 := le_antisymm hb.2 (ht1' ▸ ht.2)
    exact h1q (by rw [mem_singleton_iff, ← hLb, hb1, hαL.one])

/-- **A point of the open left arc is off the right wall** (the left-wall gap contains no contact). -/
theorem left_notMem_range_right (h : IsChangeConfigInc R L r) {t : ℝ} (ht : t ∈ Ioo (leftLo R L r) (leftHi R L r)) :
    L (arcTime t).toNNReal ∉ range R := by
  obtain ⟨-, -, -, hgL, -⟩ := h.changeCorners
  obtain ⟨-, -, -, ha, hb, -, -, -⟩ := h.changeCorner_props
  have ht1 : t < 1 := ht.2.trans_le hb.2
  intro hmem
  have hmem' : L (arcTime t).toNNReal ∈ arcRange (realPath R) := by rwa [arcRange_realPath]
  have hc := (h.right.isProperArc.cayley_mem_crossRange_iff (h.left.isProperCurve.2.2.1 _)).2 hmem'
  rw [← toDisc_eq_cayley ht1] at hc
  exact hgL.2.2.2 t ht ⟨⟨ha.1.trans ht.1.le, ht1.le⟩, hc⟩

/-- **A point of the open right arc is off the left wall.** -/
theorem right_notMem_range_left (h : IsChangeConfigInc R L r) {s : ℝ}
    (hs : s ∈ Ioo (rightLo R L r) (rightHi R L r)) : R (arcTime s).toNNReal ∉ range L := by
  obtain ⟨hg, -⟩ := h.changeCorners
  obtain ⟨hu, hv, -⟩ := h.changeCorner_props
  have hs1 : s < 1 := hs.2.trans_le hv.2
  intro hmem
  have hmem' : R (arcTime s).toNNReal ∈ arcRange (realPath L) := by rwa [arcRange_realPath]
  have hc := (h.left.isProperArc.cayley_mem_crossRange_iff (h.right.isProperCurve.2.2.1 _)).2 hmem'
  rw [← toDisc_eq_cayley hs1] at hc
  exact hg.2.2.2 s hs ⟨⟨hu.1.trans hs.1.le, hs1.le⟩, hc⟩

/-- **The boundary points with a nonzero real value of `Ψ` lie on the open arcs.** -/
theorem mem_open_arcs (h : IsChangeConfigInc R L r)
    (hU : IsBdryUniformizer (cayley '' changePocket R L r) (openPt R L r) (closePt R L r) Ψ) {z : ℂ}
    (hz : z ∈ closure (cayley '' changePocket R L r) \ {closePt R L r}) (hzr : (Ψ z).im = 0) (hz0 : Ψ z ≠ 0) :
    (∃ s ∈ Ioo (rightLo R L r) (rightHi R L r), toDisc (realPath R) s = z) ∨
      (∃ t ∈ Ioo (leftLo R L r) (leftHi R L r), toDisc (realPath L) t = z) := by
  obtain ⟨-, -, -, -, -, -, hLa, hLb⟩ := h.changeCorner_props
  have hzD : z ∉ cayley '' changePocket R L r := fun hzD => by
    have : (0 : ℝ) < (Ψ z).im := hU.conf.2.mapsTo hzD
    rw [hzr] at this; exact lt_irrefl _ this
  have hfr : z ∈ frontier (cayley '' changePocket R L r) := by
    rw [(isOpen_cayley h).frontier_eq]; exact ⟨hz.1, hzD⟩
  have hzq : z ≠ closePt R L r := hz.2
  rw [frontier_eq h] at hfr
  rcases hfr with ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩
  · left
    refine ⟨s, ⟨lt_of_le_of_ne hs.1 fun he => hz0 ?_, lt_of_le_of_ne hs.2 fun he => hzq ?_⟩, rfl⟩
    · rw [← he]; exact hU.zero
    · rw [he]; rfl
  · right
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 fun he => hz0 ?_, lt_of_le_of_ne ht.2 fun he => hzq ?_⟩, rfl⟩
    · rw [← he, hLa]; exact hU.zero
    · rw [he, hLb]

theorem toNNReal_arcTime_lt {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t < 1) :
    (arcTime s).toNNReal < (arcTime t).toNNReal :=
  (Real.toNNReal_lt_toNNReal_iff (arcTime_pos ⟨hs.trans_lt hst, ht⟩)).2
    (strictMonoOn_arcTime ⟨hs, hst.trans ht⟩ ⟨(hs.trans_lt hst).le, ht⟩ hst)

theorem discTime_toNNReal_arcTime {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    discTime ((arcTime s).toNNReal : ℝ) = s := by
  rw [Real.coe_toNNReal _ (arcTime_nonneg hs), discTime_arcTime hs.2]

theorem discTime_le_discTime {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t') : discTime t ≤ discTime t' := by
  rcases eq_or_lt_of_le htt' with rfl | hlt
  · exact le_rfl
  · exact (discTime_lt_discTime ht hlt).le

end Disc

/-! ### The common-contact order after the pocket -/

section Order

/-- **A later point of the right wall is not an earlier point of the left wall** (increasing contact order: a contact
`R(u) = L(s)` with `R`-time after the opening contact and `L`-time before the closing contact would be a contact of
`L` in the gap or before the opening contact, against strict monotonicity of the contact map). -/
theorem tail_ne_left (h : IsChangeConfigInc R L r) {u s : ℝ≥0} (hu : rightLo R L r < discTime u)
    (hs : discTime s < leftHi R L r) : R u ≠ L s := by
  intro he
  obtain ⟨hg, hj1, -, hgL, -⟩ := h.changeCorners
  have hαL := h.isDiscCrosscut_left
  have hu' := discTime_mem_Icc u
  have hs' := discTime_mem_Icc s
  have hRL : toDisc (realPath R) (discTime u) = toDisc (realPath L) (discTime s) := by
    rw [toDisc_realPath_discTime, toDisc_realPath_discTime, he]
  have hsC : discTime (s : ℝ) ∈ Sec7.pocketContactSet (toDisc (realPath L)) (toDisc (realPath R)) :=
    ⟨hs', _, hu', hRL⟩
  have hsa : discTime (s : ℝ) ≤ leftLo R L r := by
    by_contra hlt
    exact hgL.2.2.2 _ ⟨not_le.1 hlt, hs⟩ hsC
  have huC : discTime (u : ℝ) ∈ Sec7.pocketContactSet (toDisc (realPath R)) (toDisc (realPath L)) :=
    ⟨hu', _, hs', hRL.symm⟩
  have hjm : contactMap (toDisc (realPath R)) (toDisc (realPath L)) (discTime u) = discTime s :=
    contactMap_eq hαL hs' hRL
  have hlt := h.inc hg.1 huC hu
  rw [hj1, hjm] at hlt
  exact absurd hsa (not_le.2 hlt)

/-- The midpoint of the selected left arc. -/
def midL (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ := (leftLo R L r + leftHi R L r) / 2

/-- The midpoint of the selected right arc. -/
def midR (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ := (rightLo R L r + rightHi R L r) / 2

/-- The left corner time: the left wall's original time at the midpoint of its selected arc. -/
def cornerL (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ≥0 := (arcTime (midL R L r)).toNNReal

/-- The right corner time. -/
def cornerR (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ≥0 := (arcTime (midR R L r)).toNNReal

/-- The escape time: a point of the open right arc beyond the right corner. -/
def escR (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ≥0 := (arcTime ((rightLo R L r + 3 * rightHi R L r) / 4)).toNNReal

/-- The opening contact's original time on the left wall. -/
def openL (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ≥0 := (arcTime (leftLo R L r)).toNNReal

/-- The opening contact's original time on the right wall. -/
def openR (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ≥0 := (arcTime (rightLo R L r)).toNNReal

/-- The arc parameters of the corner and escape times. -/
theorem corner_times (h : IsChangeConfigInc R L r) :
    openL R L r < cornerL R L r ∧ openR R L r < cornerR R L r ∧ cornerR R L r < escR R L r ∧
      discTime (cornerL R L r : ℝ) = midL R L r ∧ midL R L r < leftHi R L r ∧
      discTime (escR R L r : ℝ) = (rightLo R L r + 3 * rightHi R L r) / 4 ∧
      (rightLo R L r + 3 * rightHi R L r) / 4 ∈ Ioo (rightLo R L r) (rightHi R L r) := by
  obtain ⟨hu, hv, huv, ha, hb, hab, -, -⟩ := h.changeCorner_props
  have hmL : midL R L r < leftHi R L r := by rw [midL]; linarith
  have hmL0 : leftLo R L r < midL R L r := by rw [midL]; linarith
  have hmR : midR R L r < rightHi R L r := by rw [midR]; linarith
  have hmR0 : rightLo R L r < midR R L r := by rw [midR]; linarith
  have he1 : midR R L r < (rightLo R L r + 3 * rightHi R L r) / 4 := by rw [midR]; linarith
  have he2 : (rightLo R L r + 3 * rightHi R L r) / 4 < rightHi R L r := by linarith
  have he0 : rightLo R L r < (rightLo R L r + 3 * rightHi R L r) / 4 := by linarith
  refine ⟨toNNReal_arcTime_lt ha.1 hmL0 (hmL.trans_le hb.2), toNNReal_arcTime_lt hu.1 hmR0 (hmR.trans_le hv.2),
    toNNReal_arcTime_lt (hu.1.trans hmR0.le) he1 (he2.trans_le hv.2),
    discTime_toNNReal_arcTime ⟨ha.1.trans hmL0.le, hmL.trans_le hb.2⟩, hmL,
    discTime_toNNReal_arcTime ⟨hu.1.trans he0.le, he2.trans_le hv.2⟩, ⟨he0, he2⟩⟩

/-- **`C ⊂ D_p`** (proof of Aux. lemma 119, p. 385: "Then `C ⊂ D_p` […] That continuation avoids both retained
prefixes, by simplicity and common-contact order, and goes to the original target at infinity"): the change pocket lies
in the unbounded domain of the corner prefixes `L([0, cornerL]) ∪ R([0, cornerR])`. It escapes through the point
`R(escR)` of the open right arc along the right wall's continuation. -/
theorem subset_H_diff_fillH_corner (h : IsChangeConfigInc R L r) :
    changePocket R L r ⊆ H \ fillH (Restart.prefixSet L (cornerL R L r) R (cornerR R L r)) := by
  obtain ⟨hLR, hRR, hRe, hdL, hmL, hde, hs₃⟩ := corner_times h
  obtain ⟨hu, hv, -⟩ := h.changeCorner_props
  set Γ := Restart.prefixSet L (cornerL R L r) R (cornerR R L r) with hΓ
  set C := changePocket R L r with hCdef
  set t₃ := escR R L r with ht₃
  set s₃ := (rightLo R L r + 3 * rightHi R L r) / 4 with hs₃def
  have hs₃1 : s₃ < 1 := hs₃.2.trans_le hv.2
  have hΓc : IsClosed Γ := (Restart.isCompact_prefixSet h.left.1.continuousOn h.right.1.continuousOn).isClosed
  have hΓsub : Γ ⊆ range L ∪ range R := by
    rintro z (⟨u, -, rfl⟩ | ⟨u, -, rfl⟩)
    · exact Or.inl ⟨u, rfl⟩
    · exact Or.inr ⟨u, rfl⟩
  have hCΓ : C ⊆ H \ Γ := fun z hz => by
    obtain ⟨hzH, hzn⟩ := h.changePocket_subset hz
    exact ⟨hzH, fun hzΓ => hzn ((hΓsub hzΓ).symm)⟩
  -- the right wall after the escape time misses `Γ`
  have hR3 : R t₃ = cayleyInv (toDisc (realPath R) s₃) := (cayleyInv_toDisc h.right hs₃1).symm
  have hdisc : ∀ u : ℝ≥0, t₃ ≤ u → rightLo R L r < discTime u := fun u hu' => by
    have := discTime_le_discTime t₃.coe_nonneg (show (t₃ : ℝ) ≤ u from hu')
    rw [hde] at this
    exact hs₃.1.trans_le this
  have hnotΓ : ∀ u : ℝ≥0, t₃ ≤ u → R u ∉ Γ := by
    intro u hu' hm
    rcases hm with ⟨s, hs, hsu⟩ | ⟨s, hs, hsu⟩
    · have hsd : discTime (s : ℝ) < leftHi R L r := by
        have := discTime_le_discTime s.coe_nonneg (show (s : ℝ) ≤ cornerL R L r from hs.2)
        rw [hdL] at this
        exact this.trans_lt hmL
      exact tail_ne_left h (hdisc u hu') hsd hsu.symm
    · have := h.right.2.1 hsu
      rw [this] at hs
      exact absurd (hs.2.trans_lt hRe) (not_lt.2 hu')
  have ht₃0 : 0 < t₃ := lt_of_le_of_lt (zero_le (a := cornerR R L r)) hRe
  set X := R '' Ioi t₃ with hX
  have hXΓ : X ⊆ H \ Γ := by
    rintro _ ⟨u, hu', rfl⟩
    exact ⟨h.right.2.2.2.1 u (ht₃0.trans hu'), hnotΓ u (le_of_lt hu')⟩
  have hXc : IsPreconnected X := isPreconnected_Ioi.image R h.right.1.continuousOn
  have hXb : ¬ IsBounded X := by
    intro hb
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    obtain ⟨T, hT⟩ := eventually_atTop.1 ((tendsto_atTop.1 h.right.2.2.2.2) (M + 1))
    have h1 := hT (max T (t₃ + 1)) (le_max_left _ _)
    have h2 := hM _ ⟨max T (t₃ + 1), lt_of_lt_of_le (lt_add_one t₃) (le_max_right _ _), rfl⟩
    linarith
  have hw₀ : R t₃ ∈ H \ Γ := ⟨h.right.2.2.2.1 t₃ ht₃0, hnotΓ t₃ le_rfl⟩
  have hw₀C : R t₃ ∈ closure C := by
    have hfr : toDisc (realPath R) s₃ ∈ closure (cayley '' C) := by
      refine frontier_subset_closure ?_
      rw [frontier_eq h]
      exact Or.inl ⟨s₃, Ioo_subset_Icc_self hs₃, rfl⟩
    have hne : toDisc (realPath R) s₃ ≠ 1 := by
      rw [toDisc_eq_cayley hs₃1]; exact cayley_ne_one_of_Hbar (h.right.isProperCurve.2.2.1 _)
    have hca : ContinuousAt cayleyInv (toDisc (realPath R) s₃) :=
      QuantumZipper.CA.continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds hne)
    have hid : cayleyInv '' (cayley '' C) = C := by
      rw [image_image]
      refine (image_congr fun z hz => QuantumZipper.CA.cayleyInv_cayley
        (add_I_ne_zero_of_mem_Hbar (H_subset_Hbar' (h.changePocket_subset_H hz)))).trans (image_id _)
    have := hca.continuousWithinAt.mem_closure_image hfr
    rwa [hid, ← hR3] at this
  have hw₀X : R t₃ ∈ closure X := by
    have ht : Tendsto R (𝓝[>] t₃) (𝓝 (R t₃)) := (h.right.1.tendsto t₃).mono_left nhdsWithin_le_nhds
    exact mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun u hu' => ⟨u, hu', rfl⟩)
  exact Lemma71O.subset_H_diff_fillH_of_escape hΓc h.isConnected_changePocket.isPreconnected hCΓ hXc hXΓ hXb hw₀
    hw₀C hw₀X

end Order

/-! ### The flow chart -/

section Frame

/-- **The flow chart of the change pocket** (Aux. lemma 119: "a conformal chart `φ : C → ℍ` taking `x₀` to zero and
`y₀` to infinity"): a conformal chart `c` of the change pocket with `c.1 = Ψ ∘ cayley` there, `Ψ` a two-point
uniformizer of the Cayley image with its Jordan boundary extension (opening contact `↦ 0`, closing contact `↦ ∞`),
for a change configuration whose flow chart is oriented (the open right-wall arc goes to `ℝ₊`). -/
structure IsFlowChart (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) : Prop where
  config : IsChangeConfigInc R L r
  orient : IsFlowChartOriented R L r
  unif : IsBdryUniformizer (cayley '' changePocket R L r) (openPt R L r) (closePt R L r) Ψ
  conf : c.IsConformal
  dom : (c.dom : Set ℂ) = changePocket R L r
  eq : ∀ x ∈ changePocket R L r, c.1 x = Ψ (cayley x)

namespace IsFlowChart

variable {c : Chart}

/-- The chart inverse lands at every point of `ℍ̄`, at the inverse Cayley image of the boundary point with that value
of `Ψ`. -/
theorem exists_tendsto (hF : IsFlowChart R L r Ψ c) {q : ℂ} (hq : q ∈ Hbar) :
    ∃ z ∈ closure (cayley '' changePocket R L r) \ {closePt R L r}, Ψ z = q ∧
      Tendsto c.2.1 (𝓝[H] q) (𝓝 (cayleyInv z)) :=
  Lemma71M.tendsto_inv_of_ext hF.conf hF.dom hF.config.changePocket_subset_H (closePt_notMem hF.config)
    hF.unif.cont hF.unif.inj hF.unif.tendsto hF.eq (one_notMem hF.config) (by rw [closure_H]; exact hq)

theorem land_eq (hF : IsFlowChart R L r Ψ c) {q : ℂ} (hq : q ∈ Hbar) {z : ℂ}
    (hz : z ∈ closure (cayley '' changePocket R L r) \ {closePt R L r}) (hΨz : Ψ z = q) :
    land c q = cayleyInv z := by
  obtain ⟨z', hz', hΨz', hl⟩ := hF.exists_tendsto hq
  have hzz : z' = z := hF.unif.inj hz' hz (hΨz'.trans hΨz.symm)
  rw [land, extendFrom_eq (by rw [closure_H]; exact hq) hl, hzz]

theorem ne_one (hF : IsFlowChart R L r Ψ c) {z : ℂ}
    (hz : z ∈ closure (cayley '' changePocket R L r) \ {closePt R L r}) : z ≠ 1 := fun h1 =>
  one_notMem hF.config (h1 ▸ hz)

/-- **The landing map is injective along `ℝ`.** -/
theorem injective_land (hF : IsFlowChart R L r Ψ c) : Function.Injective fun t : ℝ => land c t := by
  intro ξ ξ' he
  have hξ : ((ξ : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hξ' : ((ξ' : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨z, hz, hΨz, -⟩ := hF.exists_tendsto hξ
  obtain ⟨z', hz', hΨz', -⟩ := hF.exists_tendsto hξ'
  have he' : cayleyInv z = cayleyInv z' := by
    have := he
    simp only at this
    rwa [hF.land_eq hξ hz hΨz, hF.land_eq hξ' hz' hΨz'] at this
  have hzz : z = z' := by
    rw [← QuantumZipper.CA.cayley_cayleyInv (hF.ne_one hz), he', QuantumZipper.CA.cayley_cayleyInv (hF.ne_one hz')]
  exact Complex.ofReal_injective (hΨz.symm.trans (hzz ▸ hΨz'))

/-- **The opening contact** lands at `0`: `land c 0 = L(openL) = R(openR)`. -/
theorem land_zero (hF : IsFlowChart R L r Ψ c) :
    land c 0 = L (openL R L r) ∧ land c 0 = R (openR R L r) := by
  have h := hF.config
  obtain ⟨-, hv, huv, -, hb, hab, hLa, -⟩ := h.changeCorner_props
  have hmem : openPt R L r ∈ closure (cayley '' changePocket R L r) \ {closePt R L r} :=
    ⟨frontier_subset_closure h.openPt_mem_frontier, h.openPt_ne_closePt⟩
  have h0 := hF.land_eq (mem_Hbar_of_im_eq_zero (by simp)) hmem hF.unif.zero
  refine ⟨?_, ?_⟩
  · rw [h0, ← hLa, cayleyInv_toDisc h.left (hab.trans_le hb.2)]; rfl
  · rw [h0, openPt, cayleyInv_toDisc h.right (huv.trans_le hv.2)]; rfl

/-- **Negative points land on the open left arc, off the right wall.** -/
theorem land_neg (hF : IsFlowChart R L r Ψ c) {ξ : ℝ} (hξ : ξ < 0) :
    ∃ s : ℝ≥0, L s ∉ range R ∧ land c ξ = L s := by
  have h := hF.config
  obtain ⟨-, -, -, -, hb, -⟩ := h.changeCorner_props
  have hξH : ((ξ : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨z, hz, hΨz, -⟩ := hF.exists_tendsto hξH
  have hl := hF.land_eq hξH hz hΨz
  rcases mem_open_arcs h hF.unif hz (by rw [hΨz]; simp) (by rw [hΨz]; exact_mod_cast hξ.ne) with
    ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩
  · have := hF.orient Ψ hF.unif s hs
    rw [hΨz] at this
    simp only [Complex.ofReal_re] at this
    linarith
  · refine ⟨(arcTime t).toNNReal, left_notMem_range_right h ht, ?_⟩
    rw [hl, cayleyInv_toDisc h.left (ht.2.trans_le hb.2)]

/-- **Positive points land on the open right arc, off the left wall.** -/
theorem land_pos (hF : IsFlowChart R L r Ψ c) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ s : ℝ≥0, R s ∉ range L ∧ land c ξ = R s := by
  have h := hF.config
  obtain ⟨-, hv, -⟩ := h.changeCorner_props
  have hξH : ((ξ : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨z, hz, hΨz, -⟩ := hF.exists_tendsto hξH
  have hl := hF.land_eq hξH hz hΨz
  rcases mem_open_arcs h hF.unif hz (by rw [hΨz]; simp) (by rw [hΨz]; exact_mod_cast hξ.ne') with
    ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩
  · refine ⟨(arcTime s).toNNReal, right_notMem_range_left h hs, ?_⟩
    rw [hl, cayleyInv_toDisc h.right (hs.2.trans_le hv.2)]
  · have := PocketCoord.IsChangeConfigInc.re_neg_left_of_re_pos h hF.unif (hF.orient Ψ hF.unif) t ht
    rw [hΨz] at this
    simp only [Complex.ofReal_re] at this
    linarith

/-- **The flow chart of the change pocket is a two-arc frame** (walls `L` left, `R` right; corner prefixes through the
midpoints of the selected arcs). -/
theorem isTwoArcFrame (hF : IsFlowChart R L r Ψ c) :
    IsTwoArcFrame L R (changePocket R L r) c (openL R L r) (openR R L r) (cornerL R L r) (cornerR R L r) := by
  have h := hF.config
  obtain ⟨hLR, hRR, -⟩ := corner_times h
  refine ⟨h.left, h.right, hF.conf, hF.dom, ?_, ?_, fun q hq => ?_, hF.injective_land, hF.land_zero.1,
    hF.land_zero.2, fun ξ hξ => hF.land_neg hξ, fun ξ hξ => hF.land_pos hξ, hLR, hRR, subset_H_diff_fillH_corner h⟩
  · exact Set.disjoint_left.2 fun z hz hzL => (h.changePocket_subset hz).2 (Or.inr hzL)
  · exact Set.disjoint_left.2 fun z hz hzR => (h.changePocket_subset hz).2 (Or.inl hzR)
  · obtain ⟨z, -, -, hz⟩ := hF.exists_tendsto hq
    exact ⟨_, hz⟩

/-- **Aux. lemma 119's common lift for the change pocket** (pp. 385–387: "Define the lift of `log φ′` by the chain rule
[…] This is the required exact alignment of the two selected sides. […] This proves the alignment on the whole two-arc
boundary, including all finite actual angle jumps"): for every logarithm `ℓ` of the flow chart's derivative whose
imaginary part is the chart lift, one integer `n` makes `Im ℓ + 2πn` agree in boundary value with the canonical
derivative argument of every own prefix of the left wall on `ℝ₋` and of the right wall on `ℝ₊`
(`Lemma71N.IsPocketBranch L R c n`). -/
theorem exists_isPocketBranch (hF : IsFlowChart R L r Ψ c) {ℓ : ℂ → ℂ}
    (hℓ : IsDerivLog c.1 ℓ (changePocket R L r)) (hlift : ∀ z ∈ changePocket R L r, c.2.2 z = (ℓ z).im) :
    ∃ n : ℤ, Lemma71N.IsPocketBranch L R c n :=
  hF.isTwoArcFrame.exists_isPocketBranch hℓ hlift

/-- **The integer of Aux. lemma 119 is unique** once both walls are generated by drivers ("No independent integer
offset is allowed on the two sides"). -/
theorem existsUnique_isPocketBranch (hF : IsFlowChart R L r Ψ c) {ℓ : ℂ → ℂ}
    (hℓ : IsDerivLog c.1 ℓ (changePocket R L r)) (hlift : ∀ z ∈ changePocket R L r, c.2.2 z = (ℓ z).im)
    {WL WR : ℝ≥0 → ℝ} (htrL : IsGeneratingTrace WL ⊤ L) (htrR : IsGeneratingTrace WR ⊤ R) :
    ∃! n : ℤ, Lemma71N.IsPocketBranch L R c n :=
  hF.isTwoArcFrame.existsUnique_isPocketBranch hℓ hlift htrL htrR

end IsFlowChart

end Frame

end InteractingSLE.Sec7.Aux119Bdry
