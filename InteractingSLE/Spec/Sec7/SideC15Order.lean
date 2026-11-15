/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux119Bdry

/-!
# Native source-word order along the two incoming arcs

PROVE-SIDE-COLLAR2. Continuity, injectivity and the opening value zero
fix the order of the flow uniformizer along each arc. This uses the
existing real interval theorem, rather than assuming a boundary order.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex
open QuantumZipper.CA (cayley)
open scoped NNReal

namespace InteractingSLE.Sec7.SideC15

open WangWu PocketCoord PocketJordan Aux119Bdry Lemma71I

/-- A continuous injective real boundary coordinate starting at zero is
strictly increasing if all its subsequent values are positive. -/
theorem strictMonoOn_of_zero_pos {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Ico a b)) (hi : InjOn f (Ico a b)) (h0 : f a = 0)
    (hp : ∀ s ∈ Ioo a b, 0 < f s) : StrictMonoOn f (Ico a b) := by
  intro x hx y hy hxy
  have hay : a < y := hx.1.trans_lt hxy
  have hsub : Icc a y ⊆ Ico a b := fun _ hz => ⟨hz.1, hz.2.trans_lt hy.2⟩
  have h := ContinuousOn.strictMonoOn_of_injOn_Icc hay.le
    (show f a ≤ f y by rw [h0]; exact (hp y ⟨hay, hy.2⟩).le)
    (hc.mono hsub) (hi.mono hsub)
  exact h ⟨hx.1, hxy.le⟩ ⟨hay.le, le_rfl⟩ hxy

/-- The decreasing version for the negative incoming half-line. -/
theorem strictAntiOn_of_zero_neg {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Ico a b)) (hi : InjOn f (Ico a b)) (h0 : f a = 0)
    (hp : ∀ s ∈ Ioo a b, f s < 0) : StrictAntiOn f (Ico a b) := by
  have hn : InjOn (fun s => -f s) (Ico a b) := fun x hx y hy h => hi hx hy (neg_injective h)
  have h := strictMonoOn_of_zero_pos hc.neg hn (show -f a = 0 by rw [h0, neg_zero])
    (fun s hs => neg_pos.2 (hp s hs))
  intro x hx y hy hxy
  exact neg_lt_neg_iff.1 (h hx hy hxy)

/-- The flow coordinate increases on the actual right incoming arc,
from its opening value zero towards its closing pole. -/
theorem strictMonoOn_right_flowArc {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}
    (hF : IsFlowChart R L r Ψ c) :
    StrictMonoOn (fun s => (Ψ (toDisc (realPath R) s)).re)
      (Ico (rightLo R L r) (rightHi R L r)) := by
  have h := hF.config
  obtain ⟨hu, hv, _, _, _, _, _, _⟩ := h.changeCorner_props
  have hα := h.isDiscCrosscut_right
  have hsub : Ico (rightLo R L r) (rightHi R L r) ⊆ Icc (0 : ℝ) 1 :=
    fun _ hs => ⟨hu.1.trans hs.1, hs.2.le.trans hv.2⟩
  have hfr : ∀ s ∈ Ico (rightLo R L r) (rightHi R L r),
      toDisc (realPath R) s ∈ frontier (cayley '' changePocket R L r) := by
    intro s hs
    rw [Aux119Bdry.frontier_eq h]
    exact Or.inl ⟨s, ⟨hs.1, hs.2.le⟩, rfl⟩
  have hq : ∀ s ∈ Ico (rightLo R L r) (rightHi R L r),
      toDisc (realPath R) s ≠ closePt R L r := by
    intro s hs he
    exact hs.2.ne (hα.inj (hsub hs) hv he)
  have hmap : MapsTo (toDisc (realPath R)) (Ico (rightLo R L r) (rightHi R L r))
      (closure (cayley '' changePocket R L r) \ {closePt R L r}) :=
    fun s hs => ⟨frontier_subset_closure (hfr s hs), hq s hs⟩
  apply strictMonoOn_of_zero_pos
  · exact Complex.continuous_re.comp_continuousOn (hF.unif.cont.comp (hα.cont.mono hsub) hmap)
  · intro x hx y hy he
    have him := fun s hs => hF.unif.im_eq_zero (isOpen_cayley h) (closePt_notMem h) (hfr s hs) (hq s hs)
    exact hα.inj (hsub hx) (hsub hy) (hF.unif.inj (hmap hx) (hmap hy)
      (Complex.ext he ((him x hx).trans (him y hy).symm)))
  · exact congrArg Complex.re hF.unif.zero
  · exact hF.orient Ψ hF.unif

/-- The flow coordinate decreases on the actual left incoming arc. -/
theorem strictAntiOn_left_flowArc {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}
    (hF : IsFlowChart R L r Ψ c) :
    StrictAntiOn (fun s => (Ψ (toDisc (realPath L) s)).re)
      (Ico (leftLo R L r) (leftHi R L r)) := by
  have h := hF.config
  obtain ⟨_, _, _, ha, hb, _, hLa, hLb⟩ := h.changeCorner_props
  have hα := h.isDiscCrosscut_left
  have hsub : Ico (leftLo R L r) (leftHi R L r) ⊆ Icc (0 : ℝ) 1 :=
    fun _ hs => ⟨ha.1.trans hs.1, hs.2.le.trans hb.2⟩
  have hfr : ∀ s ∈ Ico (leftLo R L r) (leftHi R L r),
      toDisc (realPath L) s ∈ frontier (cayley '' changePocket R L r) := by
    intro s hs
    rw [Aux119Bdry.frontier_eq h]
    exact Or.inr ⟨s, ⟨hs.1, hs.2.le⟩, rfl⟩
  have hq : ∀ s ∈ Ico (leftLo R L r) (leftHi R L r),
      toDisc (realPath L) s ≠ closePt R L r := by
    intro s hs he
    exact hs.2.ne (hα.inj (hsub hs) hb (he.trans hLb.symm))
  have hmap : MapsTo (toDisc (realPath L)) (Ico (leftLo R L r) (leftHi R L r))
      (closure (cayley '' changePocket R L r) \ {closePt R L r}) :=
    fun s hs => ⟨frontier_subset_closure (hfr s hs), hq s hs⟩
  apply strictAntiOn_of_zero_neg
  · exact Complex.continuous_re.comp_continuousOn (hF.unif.cont.comp (hα.cont.mono hsub) hmap)
  · intro x hx y hy he
    have him := fun s hs => hF.unif.im_eq_zero (isOpen_cayley h) (closePt_notMem h) (hfr s hs) (hq s hs)
    exact hα.inj (hsub hx) (hsub hy) (hF.unif.inj (hmap hx) (hmap hy)
      (Complex.ext he ((him x hx).trans (him y hy).symm)))
  · rw [hLa]
    exact congrArg Complex.re hF.unif.zero
  · exact h.re_neg_left_of_re_pos hF.unif (hF.orient Ψ hF.unif)

end InteractingSLE.Sec7.SideC15
