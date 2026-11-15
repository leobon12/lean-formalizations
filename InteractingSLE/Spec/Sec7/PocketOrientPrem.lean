/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketMarksOrient
import InteractingSLE.Spec.Sec5.Cond44RefSide
import InteractingSLE.WangWu.MeanIdentChamber
import InteractingSLE.WangWu.Prop418Side
import InteractingSLE.Spec.Sec7.Lemma613Geom

/-!
# The flow-chart orientation of the change pocket from the side of the left wall's change point

Packet PROVE-STRIPSYS18 (specification §7.4.1, Aux. lemma 119, p. 385: "Let `C` be the Jordan pocket between two
consecutive common contacts `x₀, y₀`, with `α_R` on its right and `α_L` on its left"; proof of Aux. lemma 130, p. 412:
"Consequently `C` is on the range side of this frontier portion. Thus the second incoming arc is the left boundary of
`C` and the first is its right boundary").

PROVE-STRIPSYS17 reduced the flow-chart orientation `PocketMarks.IsFlowChartOriented R L r` (every two-point
uniformizer of the change pocket sends the open right-wall arc into `(0, ∞)`) to two topological premises: the pocket
lies on the left of the right wall (`changePocket R L r ⊆ leftSideOf (range R)`) and the open right-wall arc is reached
from the right. Here both are derived from the single geometric fact that **the left wall's change point `L r` lies
on the left of the right wall**, which is equivalent to the first premise (`changePocket_subset_leftSideOf_iff`):

* **`IsChangeConfigInc.changePocket_subset_leftSideOf_iff`**: `C ⊆ leftSideOf (range R) ↔ L r ∈ leftSideOf (range R)`;
* **`IsChangeConfigInc.exists_right_access`**: when `C` lies on the left, an interior point of the right-wall arc is
  reached from infinity through the right side of `R` (the second premise; the right side touches the positive reals
  and every point of `R` is adherent to it);
* **`IsChangeConfigInc.isFlowChartOriented_of_mem_leftSideOf`**: `L r ∈ leftSideOf (range R) → IsFlowChartOriented`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc

open WangWu Lemma71I PocketJordan PocketMarks

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- The left side of the right wall is open. -/
theorem isOpen_leftSideOf_right (h : IsChangeConfigInc R L r) : IsOpen (leftSideOf (range R)) := by
  have := Sec5.Cond44Ref.isOpen_leftSideOf_arcRange h.right.isProperArc
  rwa [arcRange_realPath] at this

/-- The left and right sides of the right wall are disjoint. -/
theorem disjoint_sides_right (h : IsChangeConfigInc R L r) :
    Disjoint (leftSideOf (range R)) (rightSideOf (range R)) := by
  have := h.right.isProperArc.disjoint_leftSideOf_rightSideOf
  rwa [arcRange_realPath] at this

/-- The change pocket avoids the right wall. -/
theorem changePocket_subset_compl_right (h : IsChangeConfigInc R L r) : changePocket R L r ⊆ H \ range R :=
  fun _ hw => ⟨(h.changePocket_subset hw).1, fun hR => (h.changePocket_subset hw).2 (Or.inl hR)⟩

/-- **The change pocket lies on the left of the right wall as soon as the left wall's change point does.** -/
theorem changePocket_subset_leftSideOf (h : IsChangeConfigInc R L r) (hLr : L r ∈ leftSideOf (range R)) :
    changePocket R L r ⊆ leftSideOf (range R) := by
  obtain ⟨z, hzl, hzC⟩ := mem_closure_iff.1 h.mem_closure_changePocket _ h.isOpen_leftSideOf_right hLr
  have hcc : changePocket R L r ⊆ connectedComponentIn (H \ range R) z :=
    h.isConnected_changePocket.isPreconnected.subset_connectedComponentIn hzC h.changePocket_subset_compl_right
  exact fun w hw => mem_leftSideOf_of_mem_connectedComponentIn hzl (hcc hw)

/-- **The pocket's side of the right wall is the side of the left wall's change point**:
`changePocket R L r ⊆ leftSideOf (range R)` iff `L r ∈ leftSideOf (range R)`. So the orientation premise of
`isFlowChartOriented_of_leftSideOf` is exactly the source's "with `α_L` on its left" at the change point. -/
theorem changePocket_subset_leftSideOf_iff (h : IsChangeConfigInc R L r) :
    changePocket R L r ⊆ leftSideOf (range R) ↔ L r ∈ leftSideOf (range R) := by
  refine ⟨fun hCl => ?_, h.changePocket_subset_leftSideOf⟩
  have hA := h.right.isProperArc
  have hLrH : L r ∈ H := h.left.2.2.2.1 r h.pos
  have hLA : L r ∉ arcRange (realPath R) := by rw [arcRange_realPath]; exact h.off
  rcases hA.mem_leftSideOf_or_mem_rightSideOf hLrH hLA with hl | hr
  · rwa [arcRange_realPath] at hl
  · exfalso
    rw [arcRange_realPath] at hr
    have hro : IsOpen (rightSideOf (range R)) := by
      have := Sec5.Cond44Ref.isOpen_rightSideOf_arcRange hA
      rwa [arcRange_realPath] at this
    obtain ⟨z, hzr, hzC⟩ := mem_closure_iff.1 h.mem_closure_changePocket _ hro hr
    exact Set.disjoint_left.1 h.disjoint_sides_right (hCl hzC) hzr

/-- The frontier of the change pocket's Cayley image lies on the right-wall crosscut and the Cayley image of the
left wall. -/
theorem frontier_cayley_subset (h : IsChangeConfigInc R L r) :
    frontier (cayley '' changePocket R L r) ⊆
      Lemma71K.wallPt R '' Icc 0 1 ∪ cayley '' range L := by
  obtain ⟨-, hj1, hj2, -, -, -⟩ := h.changeCorners
  obtain ⟨-, -, hfr⟩ := h.cayleyChange_props
  obtain ⟨hu, hv, -, ha, hb, -⟩ := h.changeCorner_props
  rw [hfr, pocketCurve, hj1, hj2]
  rintro w (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
  · exact Or.inl ⟨s, ⟨hu.1.trans hs.1, hs.2.trans hv.2⟩, rfl⟩
  · rcases (hs.2.trans hb.2).lt_or_eq with hs1 | hs1
    · right
      refine ⟨_, ⟨(arcTime s).toNNReal, rfl⟩, ?_⟩
      rw [toDisc_of_lt hs1]
      rfl
    · left
      refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      rw [hs1, Lemma71K.wallPt, toDisc_one, toDisc_one]

/-- **The open right-wall arc is reached from the right** when the change pocket lies on the left of the right wall:
an interior point `p` of the arc (off the upper semicircle) is adherent to an unbounded preconnected set avoiding the
closed pocket, the right-wall crosscut and the upper semicircle (the second premise of
`isFlowChartOriented_of_leftSideOf`). The set is the Cayley image of the right side of `R` (which touches the positive
reals and has every point of `R` in its closure) joined to a ray from the image of a positive real. -/
theorem exists_right_access (h : IsChangeConfigInc R L r) (hCl : changePocket R L r ⊆ leftSideOf (range R)) :
    ∃ p ∈ toDisc (realPath R) '' Ioo (rightLo R L r) (rightHi R L r), p ∉ semiArc 1 ∧
      ∃ V : Set ℂ, IsPreconnected V ∧ ¬ IsBounded V ∧ p ∈ closure V ∧
        Disjoint V (closure (cayley '' changePocket R L r) ∪ toDisc (realPath R) '' Icc 0 1 ∪ semiArc 1) := by
  obtain ⟨hu, hv, huv, -⟩ := h.changeCorner_props
  have hA := h.right.isProperArc
  have hαR := h.isDiscCrosscut_right
  set s₀ : ℝ := (rightLo R L r + rightHi R L r) / 2 with hs₀def
  have hs₀ : s₀ ∈ Ioo (rightLo R L r) (rightHi R L r) := ⟨by linarith, by linarith⟩
  have hs₀1 : s₀ ∈ Ioo (0 : ℝ) 1 := ⟨hu.1.trans_lt hs₀.1, hs₀.2.trans_le hv.2⟩
  set t₀ : ℝ≥0 := (arcTime s₀).toNNReal with ht₀
  have hp : toDisc (realPath R) s₀ = cayley (R t₀) := by
    rw [toDisc_of_lt hs₀1.2]
    rfl
  -- a point on the right side, its component, and a positive real adherent to it
  obtain ⟨ε, hε, hball⟩ := hA.exists_ball_inter_H_subset_rightSideOf one_pos
  have hz' : (1 + ((ε / 2 : ℝ) : ℂ) * I) ∈ rightSideOf (range R) := by
    rw [← arcRange_realPath]
    refine hball ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, show (1 + ((ε / 2 : ℝ) : ℂ) * I) - ((1 : ℝ) : ℂ) = ((ε / 2 : ℝ) : ℂ) * I by
        push_cast; ring, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · show (0 : ℝ) < (1 + ((ε / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, one_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, zero_add, mul_one]
      linarith
  set z' := 1 + ((ε / 2 : ℝ) : ℂ) * I with hz'def
  obtain ⟨-, x, hx, hxR, hxcl⟩ := id hz'
  set K := connectedComponentIn (H \ range R) z' with hKdef
  have hKr : K ⊆ rightSideOf (range R) := fun w hw => mem_rightSideOf_of_mem_connectedComponentIn hz' hw
  have hdisj : Disjoint K (changePocket R L r) := h.disjoint_sides_right.symm.mono hKr hCl
  have hrsK : rightSideOf (range R) ⊆ K := by
    have hpc := hA.isPreconnected_rightSideOf
    rw [arcRange_realPath] at hpc
    exact hpc.subset_connectedComponentIn hz' fun w hw => hw.1
  have hRt : R t₀ ∈ closure K := closure_mono hrsK (Lemma613.mem_closure_rightSideOf h.right t₀)
  have hRH : R t₀ ∈ Hbar := h.right.isProperCurve.2.2.1 t₀
  have hpK : toDisc (realPath R) s₀ ∈ closure (cayley '' K) := by
    rw [hp]
    exact mem_closure_image (continuousAt_cayley_of_mem_Hbar hRH) hRt
  have hLH : range L ⊆ Hbar := by
    rintro _ ⟨t, rfl⟩
    exact h.left.isProperCurve.2.2.1 t
  have hxL : (x : ℂ) ∉ range L := by
    rintro ⟨t, ht⟩
    rcases eq_zero_or_pos t with ht0 | ht0
    · rw [ht0, h.left.2.2.1] at ht
      exact hx.ne (by exact_mod_cast ht)
    · have := h.left.2.2.2.1 t ht0
      rw [ht] at this
      have h0 : (0 : ℝ) < (x : ℂ).im := this
      simp at h0
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := Theorem14.GW3.exists_right_of_component h.right.isProperCurve h.right.2.2.1
    hLH h.isOpen_changePocket h.changePocket_subset_H h.frontier_cayley_subset hdisj hx hxR hxL hxcl hpK
  refine ⟨_, ⟨s₀, hs₀, rfl⟩, fun hm => ?_, V, hV1, hV2, hV3, hV4⟩
  have := hαR.mem_disc s₀ hs₀1
  rw [mem_ball_zero_iff, hm.1] at this
  exact lt_irrefl _ this

/-- **The flow-chart orientation of the change pocket from the side of the left wall's change point** (Aux. lemma 119:
"with `α_R` on its right and `α_L` on its left"; Aux. lemma 130's proof, p. 412): if `L r` lies on the left of the
right wall, every two-point uniformizer of the change pocket sends the open right-wall arc into `(0, ∞)`. -/
theorem isFlowChartOriented_of_mem_leftSideOf (h : IsChangeConfigInc R L r) (hLr : L r ∈ leftSideOf (range R)) :
    IsFlowChartOriented R L r :=
  h.isFlowChartOriented_of_leftSideOf (h.changePocket_subset_leftSideOf hLr)
    (h.exists_right_access (h.changePocket_subset_leftSideOf hLr))

end InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc
