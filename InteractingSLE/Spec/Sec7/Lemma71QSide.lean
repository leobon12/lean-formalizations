/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71NProb
import InteractingSLE.Spec.Sec7.Lemma71JPocket
import InteractingSLE.Spec.Sec6.Prop61Three
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# Lemma 7.1's side limits along the middle curve: the sides of the middle curve and the pair components

Packet PROVE-LEMMA71Q (specification Remark 6.7, `source/spec/p145-192.md` L566–L590: "On each boundary side incident
to the active component, compare `A(τ) ⊆ A` using Proposition 3.8 … The full-curve mean on that side is the mean of the
appropriate adjacent pair. Contacts with the other outer curve cause no extra exception, since that curve avoids the
relevant component and Proposition 3.9 removes it").

Deterministic part of the probabilistic half (CS-prob) of Lemma 7.1's side limits along the middle curve `γ` between
the walls `β` (left) and `α` (right):

* `closureSide`, `measurable_closureSide`, `measurable_closureRightSide`, `measurable_closureLeftSide`: the relative
  closure of a set together with its side facing a real set `I` is a hitting-measurable function of the set (so the
  union of the remaining components is measurable from the set, as Proposition 3.9 requires);
* `disjoint_range_leftSideOf_of_subset_closedLeftSide`: if `γ` lies in the closed left side of `α`, then `α` avoids the
  left side of `γ` (the order read from the other curve);
* `leftSideOf_diff_subset_compl_closureRightSide`, `range_inter_H_subset_closureRightSide`, and their mirror images:
  the side of `γ` away from the other wall lies in the union of the components of `ℍ ∖ (wall ∪ γ)` not facing the far
  real half-line, and the other wall lies in the closure of the far side;
* `isUnionComponents_compl_closureSide`: the complement of `closureSide` is a union of components.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71Q

open QuantumZipper (H)
open LocalSets Lemma71I

/-! ### The relative closure with one side: a hitting-measurable function -/

section Meas

/-- The relative closure of `A` in `ℍ` together with the side of it facing the real set `I`. Its complement in `ℍ`
is the union of the components of `ℍ ∖ cl_ℍ A` not facing `I`. -/
def closureSide (I : Set ℝ) (A : Set ℂ) : Set ℂ := relClosureH A ∪ WangWu.sideOf I (relClosureH A)

theorem isOpen_sideOf_relClosureH (I : Set ℝ) (A : Set ℂ) : IsOpen (WangWu.sideOf I (relClosureH A)) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  exact ⟨connectedComponentIn (H \ relClosureH A) z, fun w hw => WangWu.mem_sideOf_of_mem_connectedComponentIn hz hw,
    (isOpen_H_diff_relClosureH A).connectedComponentIn, mem_connectedComponentIn hz.1⟩

theorem closureSide_subset_H (I : Set ℝ) (A : Set ℂ) : closureSide I A ⊆ H :=
  union_subset (relClosureH_subset A) fun _ hz => hz.1.1

/-- **The relative closure with its side facing `I` is a hitting-measurable function of the set**, as soon as side
membership of each point of `ℍ` is a hitting-measurable condition. -/
theorem measurable_closureSide {I : Set ℝ}
    (hmem : ∀ z ∈ H, MeasurableSet[hittingSigma] {A : Set ℂ | z ∈ WangWu.sideOf I (relClosureH A)}) :
    Measurable[hittingSigma, hittingSigma] (closureSide I) := by
  refine @measurable_generateFrom (Set ℂ) (Set ℂ) hittingSigma _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have e : closureSide I ⁻¹' {S | (S ∩ U).Nonempty} =
      {A : Set ℂ | (A ∩ U).Nonempty} ∪ ⋃ a : ℚ, ⋃ b : ℚ,
        {A : Set ℂ | WangWu.ratPt a b ∈ U ∧ WangWu.ratPt a b ∈ WangWu.sideOf I (relClosureH A)} := by
    ext A
    simp only [mem_preimage, mem_ofPred_eq, closureSide, union_inter_distrib_right, union_nonempty, mem_union,
      mem_iUnion]
    refine or_congr (relClosureH_inter_nonempty_iff hU hUH) ⟨fun ⟨z, hzS, hzU⟩ => ?_,
      fun ⟨a, b, h1, h2⟩ => ⟨_, h2, h1⟩⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ((isOpen_sideOf_relClosureH I A).inter hU) z ⟨hzS, hzU⟩
    obtain ⟨a, b, hab⟩ := WangWu.exists_ratPt_dist_lt z hε
    exact ⟨a, b, (hball hab).2, (hball hab).1⟩
  rw [e]
  refine (measurableSet_hitting hU hUH).union (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => ?_)
  by_cases hab : WangWu.ratPt a b ∈ U
  · have e' : {A : Set ℂ | WangWu.ratPt a b ∈ U ∧ WangWu.ratPt a b ∈ WangWu.sideOf I (relClosureH A)} =
        {A : Set ℂ | WangWu.ratPt a b ∈ WangWu.sideOf I (relClosureH A)} := by
      ext A
      simp only [mem_ofPred_eq, hab, true_and]
    rw [e']
    exact hmem _ (hUH hab)
  · have e' : {A : Set ℂ | WangWu.ratPt a b ∈ U ∧ WangWu.ratPt a b ∈ WangWu.sideOf I (relClosureH A)} = ∅ := by
      ext A
      simp only [mem_ofPred_eq, hab, false_and, mem_empty_iff_false]
    rw [e']
    exact @MeasurableSet.empty _ hittingSigma

/-- The relative closure with its right side is a hitting-measurable function of the set. -/
theorem measurable_closureRightSide : Measurable[hittingSigma, hittingSigma] (closureSide (Ioi 0)) :=
  measurable_closureSide fun _ hz => Lemma71Pin.measurableSet_mem_rightSideOf_relClosureH hz

/-- The relative closure with its left side is a hitting-measurable function of the set. -/
theorem measurable_closureLeftSide : Measurable[hittingSigma, hittingSigma] (closureSide (Iio 0)) :=
  measurable_closureSide fun _ hz => Lemma71Pin.measurableSet_mem_leftSideOf_relClosureH hz

/-- The complement in `ℍ` of `closureSide I A` is a union of components of `ℍ ∖ A`, when `A ⊆ ℍ` is relatively
closed. -/
theorem compl_closureSide_components {I : Set ℝ} {A : Set ℂ} (hAH : A ⊆ H) (hAo : IsOpen (H \ A)) :
    H \ closureSide I A ⊆ H \ A ∧
      ∀ z ∈ H \ closureSide I A, connectedComponentIn (H \ A) z ⊆ H \ closureSide I A := by
  have hrel : relClosureH A = A := relClosureH_eq hAH hAo
  have hsub : H \ closureSide I A ⊆ H \ A := fun z hz => ⟨hz.1, fun hzA => hz.2 (Or.inl (by rw [hrel]; exact hzA))⟩
  refine ⟨hsub, fun z hz w hw => ⟨(connectedComponentIn_subset _ _ hw).1, ?_⟩⟩
  rintro (hwA | hwS)
  · exact (connectedComponentIn_subset _ _ hw).2 (hrel ▸ hwA)
  · have hzw : z ∈ connectedComponentIn (H \ relClosureH A) w := by
      rw [hrel, ← connectedComponentIn_eq hw]
      exact mem_connectedComponentIn (hsub hz)
    exact hz.2 (Or.inr (WangWu.mem_sideOf_of_mem_connectedComponentIn hwS hzw))

end Meas

/-! ### The sides of the middle curve and the pair components -/

section Sides

variable {β α γ : ℝ≥0 → ℂ}

theorem ofReal_notMem_H (x : ℝ) : (x : ℂ) ∉ H := fun h => by
  have h' : (0 : ℝ) < (x : ℂ).im := h
  simp at h'

/-- **The order read from the other curve**: if `γ` lies in the closed left side of `α`, then `α` avoids the left side
of `γ`. -/
theorem disjoint_range_leftSideOf_of_subset_closedLeftSide (hγ : IsSimpleProper γ) (hα : IsSimpleProper α)
    (hγα : range γ ⊆ closedLeftSide α) : Disjoint (range α) (leftSideOf (range γ)) := by
  have hγ' := hγ.isProperArc
  have hα' := hα.isProperArc
  have h1 := disjoint_rightSideOf_of_subset_closedLeftSide hα.isProperCurve hα.2.2.1 hγα
  rw [← arcRange_realPath γ, ← arcRange_realPath α] at h1
  have h2 := WangWu.IsDiscCrosscut.disjoint_crossRange_crossSide_swap hα'.isDiscCrosscut_toDisc
    hγ'.isDiscCrosscut_toDisc ((WangWu.disjoint_rightSideOf_iff hα' hγ').1 h1)
  rw [Set.disjoint_left]
  intro z hzα hzL
  have hzH : z ∈ H := hzL.1.1
  have hzα' : z ∈ WangWu.arcRange (realPath α) := by rw [arcRange_realPath]; exact hzα
  have hzL' : z ∈ leftSideOf (WangWu.arcRange (realPath γ)) := by rw [arcRange_realPath]; exact hzL
  exact Set.disjoint_left.1 h2 ((hα'.cayley_mem_crossRange_iff (le_of_lt (show (0 : ℝ) < z.im from hzH))).2 hzα')
    ((hγ'.mem_leftSideOf_iff hzH).1 hzL')

/-- A positive real point is not in the closure of the left side of a simple proper curve. -/
theorem ofReal_notMem_closure_leftSideOf (hγ : IsSimpleProper γ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ∉ closure (leftSideOf (range γ)) := by
  intro hcl
  obtain ⟨r, hr, hsub⟩ := hγ.isProperArc.exists_ball_inter_H_subset_rightSideOf hx
  obtain ⟨z, hzb, hzL⟩ := mem_closure_iff.1 hcl _ isOpen_ball (mem_ball_self hr)
  have hzR := hsub ⟨hzb, hzL.1.1⟩
  rw [arcRange_realPath] at hzR
  have hd := hγ.isProperArc.disjoint_leftSideOf_rightSideOf
  rw [arcRange_realPath] at hd
  exact Set.disjoint_left.1 hd hzL hzR

/-- A negative real point is not in the closure of the right side of a simple proper curve. -/
theorem ofReal_notMem_closure_rightSideOf (hγ : IsSimpleProper γ) {x : ℝ} (hx : x < 0) :
    (x : ℂ) ∉ closure (rightSideOf (range γ)) := by
  intro hcl
  obtain ⟨r, hr, hsub⟩ := hγ.isProperArc.exists_ball_inter_H_subset_leftSideOf hx
  obtain ⟨z, hzb, hzR⟩ := mem_closure_iff.1 hcl _ isOpen_ball (mem_ball_self hr)
  have hzL := hsub ⟨hzb, hzR.1.1⟩
  rw [arcRange_realPath] at hzL
  have hd := hγ.isProperArc.disjoint_leftSideOf_rightSideOf
  rw [arcRange_realPath] at hd
  exact Set.disjoint_left.1 hd hzL hzR

/-- The union of two simple proper curves is relatively closed in `ℍ`. -/
theorem isOpen_H_diff_pair (hβ : IsSimpleProper β) (hγ : IsSimpleProper γ) :
    IsOpen (H \ ((range β ∪ range γ) ∩ H)) := by
  have e : H \ ((range β ∪ range γ) ∩ H) = H ∩ (range β ∪ range γ)ᶜ := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    tauto
  rw [e]
  exact QuantumZipper.isOpen_H.inter
    ((Lemma71Pin.IsSimpleProper.isClosed_range hβ).union (Lemma71Pin.IsSimpleProper.isClosed_range hγ)).isOpen_compl

/-- **Left side of the middle curve**: off the left wall `β`, the left side of `γ` lies in the union of the components
of `ℍ ∖ (β ∪ γ)` not facing the positive half-line. -/
theorem leftSideOf_diff_subset (hβ : IsSimpleProper β) (hγ : IsSimpleProper γ) :
    leftSideOf (range γ) \ range β ⊆ H \ closureSide (Ioi 0) ((range β ∪ range γ) ∩ H) := by
  set E := (range β ∪ range γ) ∩ H with hEdef
  have hrel : relClosureH E = E := relClosureH_eq inter_subset_right (isOpen_H_diff_pair hβ hγ)
  rintro z ⟨hzL, hzβ⟩
  have hzE : z ∉ E := fun h => h.1.elim hzβ hzL.1.2
  refine ⟨hzL.1.1, ?_⟩
  rw [closureSide, hrel]
  rintro (hz | hz)
  · exact hzE hz
  · obtain ⟨-, x, hx, -, hxcl⟩ := hz
    have h1 : connectedComponentIn (H \ E) z ⊆ connectedComponentIn (H \ range γ) z :=
      connectedComponentIn_mono z fun w hw => ⟨hw.1, fun hwγ => hw.2 ⟨Or.inr hwγ, hw.1⟩⟩
    have hsub : connectedComponentIn (H \ E) z ⊆ leftSideOf (range γ) := fun w hw =>
      WangWu.mem_leftSideOf_of_mem_connectedComponentIn hzL (h1 hw)
    exact ofReal_notMem_closure_leftSideOf hγ hx (closure_mono hsub hxcl)

/-- **Right side of the middle curve**: off the right wall `α`, the right side of `γ` lies in the union of the
components of `ℍ ∖ (α ∪ γ)` not facing the negative half-line. -/
theorem rightSideOf_diff_subset (hα : IsSimpleProper α) (hγ : IsSimpleProper γ) :
    rightSideOf (range γ) \ range α ⊆ H \ closureSide (Iio 0) ((range α ∪ range γ) ∩ H) := by
  set E := (range α ∪ range γ) ∩ H with hEdef
  have hrel : relClosureH E = E := relClosureH_eq inter_subset_right (isOpen_H_diff_pair hα hγ)
  rintro z ⟨hzR, hzα⟩
  have hzE : z ∉ E := fun h => h.1.elim hzα hzR.1.2
  refine ⟨hzR.1.1, ?_⟩
  rw [closureSide, hrel]
  rintro (hz | hz)
  · exact hzE hz
  · obtain ⟨-, x, hx, -, hxcl⟩ := hz
    have h1 : connectedComponentIn (H \ E) z ⊆ connectedComponentIn (H \ range γ) z :=
      connectedComponentIn_mono z fun w hw => ⟨hw.1, fun hwγ => hw.2 ⟨Or.inr hwγ, hw.1⟩⟩
    have hsub : connectedComponentIn (H \ E) z ⊆ rightSideOf (range γ) := fun w hw =>
      WangWu.mem_rightSideOf_of_mem_connectedComponentIn hzR (h1 hw)
    exact ofReal_notMem_closure_rightSideOf hγ hx (closure_mono hsub hxcl)

/-- **The right wall avoids the left-pair components left of `γ`**: `α ∩ ℍ` lies in the relative closure of
`β ∪ γ` together with its right side. -/
theorem range_inter_H_subset_closureRightSide (hβ : IsSimpleProper β) (hγ : IsSimpleProper γ)
    (hβγ : Disjoint (range β) (rightSideOf (range γ))) (hαγ : Disjoint (range α) (leftSideOf (range γ))) :
    range α ∩ H ⊆ closureSide (Ioi 0) ((range β ∪ range γ) ∩ H) := by
  set E := (range β ∪ range γ) ∩ H with hEdef
  have hrel : relClosureH E = E := relClosureH_eq inter_subset_right (isOpen_H_diff_pair hβ hγ)
  rintro z ⟨hzα, hzH⟩
  rw [closureSide, hrel]
  by_cases hzE : z ∈ E
  · exact Or.inl hzE
  right
  have hzγ : z ∉ range γ := fun h => hzE ⟨Or.inr h, hzH⟩
  have hzR : z ∈ rightSideOf (range γ) := by
    have h := hγ.isProperArc.mem_leftSideOf_or_mem_rightSideOf hzH (by rwa [arcRange_realPath])
    rw [arcRange_realPath] at h
    exact h.resolve_left fun hL => Set.disjoint_left.1 hαγ hzα hL
  have hsub : connectedComponentIn (H \ range γ) z ⊆ connectedComponentIn (H \ E) z := by
    refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨hzH, hzγ⟩) fun w hw => ?_
    have hwR : w ∈ rightSideOf (range γ) := WangWu.mem_rightSideOf_of_mem_connectedComponentIn hzR hw
    refine ⟨hwR.1.1, ?_⟩
    rintro ⟨hwβ | hwγ, -⟩
    · exact Set.disjoint_left.1 hβγ hwβ hwR
    · exact hwR.1.2 hwγ
  obtain ⟨-, x, hx, -, hxcl⟩ := hzR
  exact ⟨⟨hzH, hzE⟩, x, hx, fun h => ofReal_notMem_H x h.2, closure_mono hsub hxcl⟩

/-- **The left wall avoids the right-pair components right of `γ`**: `β ∩ ℍ` lies in the relative closure of
`α ∪ γ` together with its left side. -/
theorem range_inter_H_subset_closureLeftSide (hα : IsSimpleProper α) (hγ : IsSimpleProper γ)
    (hβγ : Disjoint (range β) (rightSideOf (range γ))) (hαγ : Disjoint (range α) (leftSideOf (range γ))) :
    range β ∩ H ⊆ closureSide (Iio 0) ((range α ∪ range γ) ∩ H) := by
  set E := (range α ∪ range γ) ∩ H with hEdef
  have hrel : relClosureH E = E := relClosureH_eq inter_subset_right (isOpen_H_diff_pair hα hγ)
  rintro z ⟨hzβ, hzH⟩
  rw [closureSide, hrel]
  by_cases hzE : z ∈ E
  · exact Or.inl hzE
  right
  have hzγ : z ∉ range γ := fun h => hzE ⟨Or.inr h, hzH⟩
  have hzL : z ∈ leftSideOf (range γ) := by
    have h := hγ.isProperArc.mem_leftSideOf_or_mem_rightSideOf hzH (by rwa [arcRange_realPath])
    rw [arcRange_realPath] at h
    exact h.resolve_right fun hR => Set.disjoint_left.1 hβγ hzβ hR
  have hsub : connectedComponentIn (H \ range γ) z ⊆ connectedComponentIn (H \ E) z := by
    refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨hzH, hzγ⟩) fun w hw => ?_
    have hwL : w ∈ leftSideOf (range γ) := WangWu.mem_leftSideOf_of_mem_connectedComponentIn hzL hw
    refine ⟨hwL.1.1, ?_⟩
    rintro ⟨hwα | hwγ, -⟩
    · exact Set.disjoint_left.1 hαγ hwα hwL
    · exact hwL.1.2 hwγ
  obtain ⟨-, x, hx, -, hxcl⟩ := hzL
  exact ⟨⟨hzH, hzE⟩, x, hx, fun h => ofReal_notMem_H x h.2, closure_mono hsub hxcl⟩

end Sides

/-! ### The side heights along the middle curve, pathwise -/

section Path

open Lemma71N

/-- **The side heights of the complete three-curve mean along the middle curve** (Remark 6.7 for the middle curve `γ`;
for the angle-`0` curve of Lemma 7.1, `k = χ` and `lam = λ`): at every point `γ s`, `s > 0`, approached within
`ℍ ∖ AL` along a filter on which the centred Loewner map `g_q` of the prefix `γ([0, q])` (`q > s` rational) tends to a
real `y`, the function `vL + u₀ + k Im log g_q′` tends to `−lam` if `y < 0` (the left side of `γ`) and `γ s` is off the
left wall `β`, and to `lam` if `y > 0` (the right side) and `γ s` is off the right wall `α`. -/
def MiddleSideHeight (β α γ : ℝ≥0 → ℂ) (W : ℝ≥0 → ℝ) (AL : Set ℂ) (vL u₀ : ℂ → ℝ) (k lam : ℝ) : Prop :=
  ∀ (s : ℝ≥0) (q : ℚ≥0), 0 < s → s < (q : ℝ≥0) → ∀ F : Filter ℂ, F ≤ 𝓝[H \ AL] (γ s) → ∀ y : ℝ,
    Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z) F (𝓝 (y : ℂ)) →
    (y < 0 → γ s ∉ range β → Tendsto (fun z => vL z + u₀ z +
      k * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z).im) F (𝓝 (-lam))) ∧
    (0 < y → γ s ∉ range α → Tendsto (fun z => vL z + u₀ z +
      k * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z).im) F (𝓝 lam))

variable {β α γ : ℝ≥0 → ℂ}

/-- **Proposition 3.8 for a pair `η' ∪ γ` against the middle prefix `γ([0, q])`** at a point `γ s` off `η'`, `s < q`
(the two sets agree near `γ s`: the tail of `γ` after `q` and the other curve are at positive distance). -/
theorem tendsto_pair_sub {η' : ℝ≥0 → ℂ} (hη' : IsSimpleProper η') (hγ : IsSimpleProper γ) {vE : ℂ → ℝ}
    (vq : ℚ≥0 → ℂ → ℝ)
    (hcmp : ∀ (q : ℚ≥0) (p : ℂ), p ∈ (range η' ∪ range γ) ∩ H ∪ {z : ℂ | z.im = 0} →
      p ∈ wallPrefix γ q ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, wallPrefix γ q ∩ ball p r ⊆ (range η' ∪ range γ) ∩ H) →
      (∃ r > 0, (range η' ∪ range γ) ∩ H ∩ ball p r ⊆ wallPrefix γ q) →
      Tendsto (fun z => vE z - vq q z) (𝓝[H \ ((range η' ∪ range γ) ∩ H ∪ wallPrefix γ q)] p) (𝓝 0))
    {AL : Set ℂ} (hAL : (range η' ∪ range γ) ∩ H ⊆ AL) {s : ℝ≥0} {q : ℚ≥0} (hs0 : 0 < s)
    (hsq : s < (q : ℝ≥0)) (hsη' : γ s ∉ range η') :
    Tendsto (fun z => vE z - vq q z) (𝓝[H \ AL] (γ s)) (𝓝 0) := by
  have hpH : γ s ∈ H := hγ.2.2.2.1 s hs0
  have hpB : γ s ∈ wallPrefix γ q := ⟨⟨s, by exact_mod_cast hsq.le, rfl⟩, hpH⟩
  have hBE : wallPrefix γ q ⊆ (range η' ∪ range γ) ∩ H := by
    rintro z ⟨⟨t, -, rfl⟩, hzH⟩
    exact ⟨Or.inr ⟨t, rfl⟩, hzH⟩
  have hEB : ∃ ρ > 0, (range η' ∪ range γ) ∩ H ∩ ball (γ s) ρ ⊆ wallPrefix γ q := by
    obtain ⟨ρ₁, hρ₁, h1⟩ := exists_ball_tail hγ hsq
    obtain ⟨ρ₂, hρ₂, h2⟩ := exists_ball_notMem_range hη' hsη'
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
    rintro z ⟨⟨⟨t, rfl⟩ | ⟨t, rfl⟩, hzH⟩, hzb⟩
    · exact absurd (ball_subset_ball (min_le_right _ _) hzb) (h2 t)
    · refine ⟨⟨t, ?_, rfl⟩, hzH⟩
      by_contra hlt
      have hlt' : ¬ (t : ℝ≥0∞) ≤ ((q : ℝ≥0) : ℝ≥0∞) := hlt
      have hqt : (q : ℝ≥0) ≤ t := le_of_lt (by exact_mod_cast not_le.1 hlt')
      exact h1 t hqt (ball_subset_ball (min_le_left _ _) hzb)
  refine (hcmp q (γ s) (Or.inl (hBE hpB)) (Or.inl hpB) ⟨1, one_pos, fun z hz => hBE hz.1⟩ hEB).mono_left
    (nhdsWithin_mono _ fun z hz => ⟨hz.1, ?_⟩)
  rintro (hzE | hzB)
  · exact hz.2 (hAL hzE)
  · exact hz.2 (hAL (hBE hzB))

/-- **The side heights along the middle curve, pathwise** (Remark 6.7): from the identification of the full mean with
the left pair mean `vEL` on the components of `ℍ ∖ (β ∪ γ)` not facing the positive half-line and with the right
pair mean `vER` on those of `ℍ ∖ (α ∪ γ)` not facing the negative half-line (Proposition 3.9), Proposition 3.8 for each
pair against the middle prefixes `γ([0, q])` at rational `q`, and the single-curve side heights of those prefixes. The
side of the approach is read off the sign of the real limit of `g_q` (`Lemma613.exists_pos_tendsto_of_rightSideOf`,
`Lemma71N.exists_neg_tendsto_of_leftSideOf`). -/
theorem middleSideHeight_of_pairs (hβ : IsSimpleProper β) (hα : IsSimpleProper α) (hγ : IsSimpleProper γ)
    {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (htr : IsGeneratingTrace W ⊤ γ) {AL : Set ℂ}
    (hAL : AL = (range β ∪ range α ∪ range γ) ∩ H) {vL vEL vER u₀ : ℂ → ℝ} {k lam : ℝ} (vq : ℚ≥0 → ℂ → ℝ)
    (hEqL : EqOn vL vEL (H \ closureSide (Ioi 0) ((range β ∪ range γ) ∩ H)))
    (hEqR : EqOn vL vER (H \ closureSide (Iio 0) ((range α ∪ range γ) ∩ H)))
    (hcmpL : ∀ (q : ℚ≥0) (p : ℂ), p ∈ (range β ∪ range γ) ∩ H ∪ {z : ℂ | z.im = 0} →
      p ∈ wallPrefix γ q ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, wallPrefix γ q ∩ ball p r ⊆ (range β ∪ range γ) ∩ H) →
      (∃ r > 0, (range β ∪ range γ) ∩ H ∩ ball p r ⊆ wallPrefix γ q) →
      Tendsto (fun z => vEL z - vq q z) (𝓝[H \ ((range β ∪ range γ) ∩ H ∪ wallPrefix γ q)] p) (𝓝 0))
    (hcmpR : ∀ (q : ℚ≥0) (p : ℂ), p ∈ (range α ∪ range γ) ∩ H ∪ {z : ℂ | z.im = 0} →
      p ∈ wallPrefix γ q ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, wallPrefix γ q ∩ ball p r ⊆ (range α ∪ range γ) ∩ H) →
      (∃ r > 0, (range α ∪ range γ) ∩ H ∩ ball p r ⊆ wallPrefix γ q) →
      Tendsto (fun z => vER z - vq q z) (𝓝[H \ ((range α ∪ range γ) ∩ H ∪ wallPrefix γ q)] p) (𝓝 0))
    (hsh : ∀ (q : ℚ≥0) (t₀ : ℝ≥0), t₀ < q → γ t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
      F ≤ 𝓝[H \ fillH (γ '' Icc 0 (q : ℝ≥0))] (γ t₀) → ∀ y : ℝ,
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z) F (𝓝 (y : ℂ)) →
      (0 < y → Tendsto (fun z => vq q z + u₀ z +
        k * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z).im) F (𝓝 lam)) ∧
      (y < 0 → Tendsto (fun z => vq q z + u₀ z +
        k * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z).im) F (𝓝 (-lam)))) :
    MiddleSideHeight β α γ W AL vL u₀ k lam := by
  intro s q hs0 hsq F hF y hy
  have hpH : γ s ∈ H := hγ.2.2.2.1 s hs0
  have hALγ : H \ AL ⊆ H \ range γ := fun z hz => ⟨hz.1, fun h => hz.2 (hAL ▸ ⟨Or.inr h, hz.1⟩)⟩
  have hALβ : ∀ z ∈ H \ AL, z ∉ range β := fun z hz h => hz.2 (hAL ▸ ⟨Or.inl (Or.inl h), hz.1⟩)
  have hALα : ∀ z ∈ H \ AL, z ∉ range α := fun z hz h => hz.2 (hAL ▸ ⟨Or.inl (Or.inr h), hz.1⟩)
  have hsides : ∀ z ∈ H \ range γ, z ∈ leftSideOf (range γ) ∪ rightSideOf (range γ) := by
    intro z hz
    have h := hγ.isProperArc.mem_leftSideOf_or_mem_rightSideOf hz.1 (by rw [arcRange_realPath]; exact hz.2)
    rw [arcRange_realPath] at h
    exact h
  have hfill : leftSideOf (range γ) ∪ rightSideOf (range γ) ⊆ H \ fillH (γ '' Icc 0 (q : ℝ≥0)) := by
    have h := sides_subset_H_diff_fwdHull hγ htr (q : ℝ≥0)
    rwa [SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htr ENNReal.coe_lt_top] at h
  have hEL : (range β ∪ range γ) ∩ H ⊆ AL := by
    rw [hAL]; rintro z ⟨hz | hz, hzH⟩
    · exact ⟨Or.inl (Or.inl hz), hzH⟩
    · exact ⟨Or.inr hz, hzH⟩
  have hER : (range α ∪ range γ) ∩ H ⊆ AL := by
    rw [hAL]; rintro z ⟨hz | hz, hzH⟩
    · exact ⟨Or.inl (Or.inr hz), hzH⟩
    · exact ⟨Or.inr hz, hzH⟩
  -- along an ultrafilter, the sign of the limit of `g_q` determines the side of `γ`
  have hside : ∀ U : Ultrafilter ℂ, (U : Filter ℂ) ≤ F →
      (y < 0 → leftSideOf (range γ) ∈ U) ∧ (0 < y → rightSideOf (range γ) ∈ U) := by
    intro U hU
    have hUAL : (U : Filter ℂ) ≤ 𝓝[H \ AL] (γ s) := hU.trans hF
    have hmem : leftSideOf (range γ) ∪ rightSideOf (range γ) ∈ U :=
      mem_of_superset (hUAL self_mem_nhdsWithin) fun z hz => hsides z (hALγ hz)
    have hyU := hy.mono_left hU
    constructor
    · intro hy0
      refine (Ultrafilter.union_mem_iff.1 hmem).resolve_right fun hR => ?_
      obtain ⟨y', hy', hT⟩ := Lemma613.exists_pos_tendsto_of_rightSideOf hγ hW hW0 htr hs0 hsq U
        (le_inf (hUAL.trans nhdsWithin_le_nhds) (le_principal_iff.2 hR))
      have he : (y : ℂ) = y' := tendsto_nhds_unique hyU hT
      have : y = y' := by exact_mod_cast he
      linarith
    · intro hy0
      refine (Ultrafilter.union_mem_iff.1 hmem).resolve_left fun hL => ?_
      obtain ⟨y', hy', hT⟩ := exists_neg_tendsto_of_leftSideOf hγ hW hW0 htr hs0 hsq U
        (le_inf (hUAL.trans nhdsWithin_le_nhds) (le_principal_iff.2 hL))
      have he : (y : ℂ) = y' := tendsto_nhds_unique hyU hT
      have : y = y' := by exact_mod_cast he
      linarith
  constructor
  · intro hy0 hpβ
    have hpair := tendsto_pair_sub hβ hγ vq hcmpL hEL hs0 hsq hpβ
    rw [tendsto_iff_ultrafilter]
    intro U hU
    have hUAL : (U : Filter ℂ) ≤ 𝓝[H \ AL] (γ s) := hU.trans hF
    have hLU := (hside U hU).1 hy0
    have hUL : (U : Filter ℂ) ≤ 𝓝[H \ fillH (γ '' Icc 0 (q : ℝ≥0))] (γ s) :=
      le_inf (hUAL.trans nhdsWithin_le_nhds) (le_principal_iff.2 (mem_of_superset hLU
        (subset_union_left.trans hfill)))
    have h1 := (hsh q s hsq hpH U inferInstance hUL y (hy.mono_left hU)).2 hy0
    have h2 := hpair.mono_left hUAL
    have h3 : ∀ᶠ z in (U : Filter ℂ), vL z = vEL z := by
      filter_upwards [hLU, hUAL self_mem_nhdsWithin] with z hzL hzAL
      exact hEqL (leftSideOf_diff_subset hβ hγ ⟨hzL, hALβ z hzAL⟩)
    have hsum := h2.add h1
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [h3] with z hz
    rw [hz]; ring
  · intro hy0 hpα
    have hpair := tendsto_pair_sub hα hγ vq hcmpR hER hs0 hsq hpα
    rw [tendsto_iff_ultrafilter]
    intro U hU
    have hUAL : (U : Filter ℂ) ≤ 𝓝[H \ AL] (γ s) := hU.trans hF
    have hRU := (hside U hU).2 hy0
    have hUR : (U : Filter ℂ) ≤ 𝓝[H \ fillH (γ '' Icc 0 (q : ℝ≥0))] (γ s) :=
      le_inf (hUAL.trans nhdsWithin_le_nhds) (le_principal_iff.2 (mem_of_superset hRU
        (subset_union_right.trans hfill)))
    have h1 := (hsh q s hsq hpH U inferInstance hUR y (hy.mono_left hU)).1 hy0
    have h2 := hpair.mono_left hUAL
    have h3 : ∀ᶠ z in (U : Filter ℂ), vL z = vER z := by
      filter_upwards [hRU, hUAL self_mem_nhdsWithin] with z hzR hzAL
      exact hEqR (rightSideOf_diff_subset hα hγ ⟨hzR, hALα z hzAL⟩)
    have hsum := h2.add h1
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [h3] with z hz
    rw [hz]; ring

/-- `MiddleSideHeight` does not depend on the choice of the generating driver of the middle curve. -/
theorem MiddleSideHeight.congr_driver {AL : Set ℂ} {vL u₀ : ℂ → ℝ} {k lam : ℝ} {W W' : ℝ≥0 → ℝ}
    (h : IsGeneratingTrace W ⊤ γ) (h' : IsGeneratingTrace W' ⊤ γ) (hM : MiddleSideHeight β α γ W AL vL u₀ k lam) :
    MiddleSideHeight β α γ W' AL vL u₀ k lam := by
  intro s q hs0 hsq F hF y hy
  have e1 := SideHeight.fwdMap_eq_of_isGeneratingTrace h h' (q := (q : ℝ≥0)) ENNReal.coe_lt_top
  have e2 := SideHeight.logDerivFwd_eq_of_isGeneratingTrace h h' (q := (q : ℝ≥0)) ENNReal.coe_lt_top
  rw [← e1] at hy
  rw [← e2]
  exact hM s q hs0 hsq F hF y hy

end Path

end InteractingSLE.Sec7.Lemma71Q
