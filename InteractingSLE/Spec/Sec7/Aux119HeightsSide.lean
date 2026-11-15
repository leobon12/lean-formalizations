/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketOrientPrem

/-!
# The change pocket lies on the right of the left wall

Packet PROVE-STRIPSYS25. Specification §7.4, Aux. lemma 119 (`source/spec/p385-432.md` L3, p. 385: "Let `C` be the
Jordan pocket between two consecutive common contacts `x₀, y₀`, with `α_R` on its right and `α_L` on its left"), and
its proof (L33: "Hence the own height `λ − θ_Lχ` on a right side of the left path, and `−λ − θ_Rχ` on a left side of the
right path, become exactly the two heights in (PW13.1)").

PROVE-STRIPSYS18 put the pocket on the left of the right wall (`changePocket_subset_leftSideOf`) and derived the flow
chart's orientation from it. Here the orientation gives the other side: **under the flow-chart orientation, the
change pocket lies on the right of the left wall**. If the pocket were on the left of the left wall, the orientation
theorem of PROVE-ORIENT (`Prop74B.re_pos_of_crossLoop`), applied to the left-wall crosscut with the same two-point
uniformizer (which sends the left wall's corners `L̃(leftLo) = x₀` to `0` and `L̃(leftHi) = y₀` to `∞`), would send the
open left-wall arc into `(0, ∞)`; the orientation sends it into `(−∞, 0)` (`PocketMarks.re_neg_left_of_re_pos`).

## Main results

* `leftWall_marked`: the left wall's parameters on the closed pocket are exactly `[leftLo, leftHi]`;
* `frontier_cayley_subset_leftWall`: the frontier lies on the left-wall crosscut and the right wall;
* `exists_right_access_leftWall`: an open left-wall arc point is reached from the right of the left wall when the
  pocket lies on its left;
* **`changePocket_subset_rightSideOf_left`**.

Deterministic.
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

/-- The change pocket avoids the left wall. -/
theorem changePocket_subset_compl_left (h : IsChangeConfigInc R L r) : changePocket R L r ⊆ H \ range L :=
  fun _ hw => ⟨(h.changePocket_subset hw).1, fun hL => (h.changePocket_subset hw).2 (Or.inr hL)⟩

/-- **The marked arc of the left wall**: its disc parameters on the closed Cayley image of the pocket are exactly
`[leftLo, leftHi]`. -/
theorem leftWall_marked (h : IsChangeConfigInc R L r) :
    {s ∈ Icc (0 : ℝ) 1 | toDisc (realPath L) s ∈ closure (cayley '' changePocket R L r)} =
      Icc (leftLo R L r) (leftHi R L r) := by
  obtain ⟨hg, hj1, hj2, -, -, hC⟩ := h.changeCorners
  obtain ⟨-, -, hfr⟩ := h.cayleyChange_props
  obtain ⟨hu, hv, -, ha, hb, hab, hLa, hLb⟩ := h.changeCorner_props
  have hαR := h.isDiscCrosscut_right
  have hαL := h.isDiscCrosscut_left
  obtain ⟨-, -, hdisj, -, -⟩ := pocket_props_of_strictMono hαR hαL h.inc hg
  ext s
  simp only [mem_Icc]
  constructor
  · rintro ⟨hs, hcl⟩
    rw [closure_eq_self_union_frontier, hfr] at hcl
    rcases hcl with hD | hPC
    · rw [hC] at hD
      exact absurd (Or.inr ⟨s, hs, rfl⟩) (Set.disjoint_left.1 hdisj hD)
    · rcases hPC with ⟨t, ht, he⟩ | ⟨t, ht, he⟩
      · -- a right-wall point of the pocket curve on the left wall: a contact parameter, hence a corner
        have htS : t ∈ Sec7.pocketContactSet (toDisc (realPath R)) (toDisc (realPath L)) :=
          ⟨⟨hu.1.trans ht.1, ht.2.trans hv.2⟩, s, hs, he.symm⟩
        rcases eq_or_lt_of_le ht.1 with hta | hta
        · rw [← hta] at he
          have := hαL.inj ha hs (hLa.trans he)
          exact this ▸ ⟨le_rfl, hab.le⟩
        rcases eq_or_lt_of_le ht.2 with htb | htb
        · rw [htb] at he
          have := hαL.inj hb hs (hLb.trans he)
          exact this ▸ ⟨hab.le, le_rfl⟩
        exact absurd htS (hg.2.2.2 t ⟨hta, htb⟩)
      · rw [hj1, hj2] at ht
        have := hαL.inj ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩ hs he
        exact this ▸ ht
  · intro hs
    refine ⟨⟨ha.1.trans hs.1, hs.2.trans hb.2⟩, ?_⟩
    rw [closure_eq_self_union_frontier, hfr]
    refine Or.inr (Or.inr ⟨s, ?_, rfl⟩)
    rw [hj1, hj2]
    exact hs

/-- The frontier of the change pocket's Cayley image lies on the left-wall crosscut and the Cayley image of the right
wall. -/
theorem frontier_cayley_subset_leftWall (h : IsChangeConfigInc R L r) :
    frontier (cayley '' changePocket R L r) ⊆ Lemma71K.wallPt L '' Icc 0 1 ∪ cayley '' range R := by
  obtain ⟨-, hj1, hj2, -, -, -⟩ := h.changeCorners
  obtain ⟨-, -, hfr⟩ := h.cayleyChange_props
  obtain ⟨hu, hv, -, ha, hb, -⟩ := h.changeCorner_props
  rw [hfr, pocketCurve, hj1, hj2]
  rintro w (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
  · rcases (hs.2.trans hv.2).lt_or_eq with hs1 | hs1
    · right
      refine ⟨_, ⟨(arcTime s).toNNReal, rfl⟩, ?_⟩
      rw [toDisc_of_lt hs1]
      rfl
    · left
      refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      rw [hs1, Lemma71K.wallPt, toDisc_one, toDisc_one]
  · exact Or.inl ⟨s, ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩, rfl⟩

/-- The left and right sides of the left wall are disjoint. -/
theorem disjoint_sides_left (h : IsChangeConfigInc R L r) :
    Disjoint (leftSideOf (range L)) (rightSideOf (range L)) := by
  have := h.left.isProperArc.disjoint_leftSideOf_rightSideOf
  rwa [arcRange_realPath] at this

/-- **An open left-wall arc point is reached from the right** of the left wall when the change pocket lies on its
left (the mirror image of `exists_right_access`). -/
theorem exists_right_access_leftWall (h : IsChangeConfigInc R L r)
    (hCl : changePocket R L r ⊆ leftSideOf (range L)) :
    ∃ p ∈ toDisc (realPath L) '' Ioo (leftLo R L r) (leftHi R L r), p ∉ semiArc 1 ∧
      ∃ V : Set ℂ, IsPreconnected V ∧ ¬ IsBounded V ∧ p ∈ closure V ∧
        Disjoint V (closure (cayley '' changePocket R L r) ∪ toDisc (realPath L) '' Icc 0 1 ∪ semiArc 1) := by
  obtain ⟨-, -, -, ha, hb, hab, -⟩ := h.changeCorner_props
  have hA := h.left.isProperArc
  have hαL := h.isDiscCrosscut_left
  set s₀ : ℝ := (leftLo R L r + leftHi R L r) / 2 with hs₀def
  have hs₀ : s₀ ∈ Ioo (leftLo R L r) (leftHi R L r) := ⟨by linarith, by linarith⟩
  have hs₀1 : s₀ ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans_lt hs₀.1, hs₀.2.trans_le hb.2⟩
  set t₀ : ℝ≥0 := (arcTime s₀).toNNReal with ht₀
  have hp : toDisc (realPath L) s₀ = cayley (L t₀) := by
    rw [toDisc_of_lt hs₀1.2]
    rfl
  obtain ⟨ε, hε, hball⟩ := hA.exists_ball_inter_H_subset_rightSideOf one_pos
  have hz' : (1 + ((ε / 2 : ℝ) : ℂ) * I) ∈ rightSideOf (range L) := by
    rw [← arcRange_realPath]
    refine hball ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, show (1 + ((ε / 2 : ℝ) : ℂ) * I) - ((1 : ℝ) : ℂ) = ((ε / 2 : ℝ) : ℂ) * I by
        push_cast; ring, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · show (0 : ℝ) < (1 + ((ε / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, one_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, zero_add, mul_one]
      linarith
  set z' := 1 + ((ε / 2 : ℝ) : ℂ) * I with hz'def
  obtain ⟨-, x, hx, hxL, hxcl⟩ := id hz'
  set K := connectedComponentIn (H \ range L) z' with hKdef
  have hKr : K ⊆ rightSideOf (range L) := fun w hw => mem_rightSideOf_of_mem_connectedComponentIn hz' hw
  have hdisj : Disjoint K (changePocket R L r) := h.disjoint_sides_left.symm.mono hKr hCl
  have hrsK : rightSideOf (range L) ⊆ K := by
    have hpc := hA.isPreconnected_rightSideOf
    rw [arcRange_realPath] at hpc
    exact hpc.subset_connectedComponentIn hz' fun w hw => hw.1
  have hLt : L t₀ ∈ closure K := closure_mono hrsK (Lemma613.mem_closure_rightSideOf h.left t₀)
  have hLH : L t₀ ∈ Hbar := h.left.isProperCurve.2.2.1 t₀
  have hpK : toDisc (realPath L) s₀ ∈ closure (cayley '' K) := by
    rw [hp]
    exact mem_closure_image (continuousAt_cayley_of_mem_Hbar hLH) hLt
  have hRH : range R ⊆ Hbar := by
    rintro _ ⟨t, rfl⟩
    exact h.right.isProperCurve.2.2.1 t
  have hxR : (x : ℂ) ∉ range R := by
    rintro ⟨t, ht⟩
    rcases eq_zero_or_pos t with ht0 | ht0
    · rw [ht0, h.right.2.2.1] at ht
      exact hx.ne (by exact_mod_cast ht)
    · have := h.right.2.2.2.1 t ht0
      rw [ht] at this
      have h0 : (0 : ℝ) < (x : ℂ).im := this
      simp at h0
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := Theorem14.GW3.exists_right_of_component h.left.isProperCurve h.left.2.2.1
    hRH h.isOpen_changePocket h.changePocket_subset_H h.frontier_cayley_subset_leftWall hdisj hx hxL hxR hxcl hpK
  refine ⟨_, ⟨s₀, hs₀, rfl⟩, fun hm => ?_, V, hV1, hV2, hV3, hV4⟩
  have := hαL.mem_disc s₀ hs₀1
  rw [mem_ball_zero_iff, hm.1] at this
  exact lt_irrefl _ this

/-- Under the flow-chart orientation the change pocket is not on the left of the left wall. -/
theorem not_changePocket_subset_leftSideOf_left (h : IsChangeConfigInc R L r) (hor : IsFlowChartOriented R L r) :
    ¬ changePocket R L r ⊆ leftSideOf (range L) := by
  intro hCl
  obtain ⟨Ψ, hU⟩ := h.exists_isBdryUniformizer
  obtain ⟨hg, -, -, -, -, -⟩ := h.changeCorners
  obtain ⟨-, -, -, ha, hb, hab, hLa, hLb⟩ := h.changeCorner_props
  have hαR := h.isDiscCrosscut_right
  have hαL := h.isDiscCrosscut_left
  obtain ⟨-, -, hdisj, -, -⟩ := pocket_props_of_strictMono hαR hαL h.inc hg
  obtain ⟨-, -, -, hC⟩ := h.changePocket_eq
  have hCα : ∀ x ∈ changePocket R L r, cayley x ∉ toDisc (realPath L) '' Icc 0 1 := fun x hx hm => by
    have hD : cayley x ∈ cayley '' changePocket R L r := mem_image_of_mem _ hx
    obtain ⟨-, -, -, -, -, hC'⟩ := h.changeCorners
    rw [hC'] at hD
    exact Set.disjoint_left.1 hdisj hD (Or.inr hm)
  have hcont := hU.cont
  have hinj := hU.inj
  have hmaps := hU.mapsTo
  have htend := hU.tendsto
  rw [← hLb] at hcont hinj hmaps htend
  have hzero : Ψ (toDisc (realPath L) (leftLo R L r)) = 0 := by rw [hLa]; exact hU.zero
  have hpos := Prop74B.re_pos_of_crossLoop hαL.cont hαL.inj hαL.zero hαL.one h.isOpen_changePocket
    h.isConnected_changePocket.isPreconnected h.changePocket_subset_H hCα ha.1 hab hb.2 h.leftWall_marked
    (isConformalBijection_comp hU.conf (Lemma71F.isConformalBijection_cayley_image h.changePocket_subset_H))
    hcont hinj hmaps hzero htend (fun _ _ => rfl)
    (Theorem14.GW3.windNum_crossLoop_of_subset_leftSideOf h.left.isProperCurve h.left.2.2.1 hCl)
    (h.exists_right_access_leftWall hCl)
  have hneg := h.re_neg_left_of_re_pos hU (hor Ψ hU)
  set t : ℝ := (leftLo R L r + leftHi R L r) / 2
  have ht : t ∈ Ioo (leftLo R L r) (leftHi R L r) := ⟨by simp only [t]; linarith, by simp only [t]; linarith⟩
  exact lt_asymm (hpos t ht) (hneg t ht)

/-- **The change pocket lies on the right of the left wall** under the flow-chart orientation (Aux. lemma 119: "with
`α_R` on its right and `α_L` on its left"; the own height `λ − θ_Lχ` is the right-side height of the left path). -/
theorem changePocket_subset_rightSideOf_left (h : IsChangeConfigInc R L r) (hor : IsFlowChartOriented R L r) :
    changePocket R L r ⊆ rightSideOf (range L) := by
  intro z hz
  have hzL := h.changePocket_subset_compl_left hz
  have hA := h.left.isProperArc
  rcases hA.mem_leftSideOf_or_mem_rightSideOf hzL.1 (by rw [arcRange_realPath]; exact hzL.2) with hl | hr
  · exfalso
    rw [arcRange_realPath] at hl
    refine h.not_changePocket_subset_leftSideOf_left hor fun w hw => ?_
    have hcc : changePocket R L r ⊆ connectedComponentIn (H \ range L) z :=
      h.isConnected_changePocket.isPreconnected.subset_connectedComponentIn hz h.changePocket_subset_compl_left
    exact mem_leftSideOf_of_mem_connectedComponentIn hl (hcc hw)
  · rwa [arcRange_realPath] at hr

end InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc
