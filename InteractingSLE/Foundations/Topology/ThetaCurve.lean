/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberJordan
import InteractingSLE.Spec.Sec7.InteractionLens
import QuantumZipper.Proofs.Complex.TopoJaniszewski

/-!
# The θ-curve theorem

Packet PROVE-R16: "the θ-curve form of Jordan separation that the gate lemma (Lemma 1.3) needs"
(ruling R41, `source/external/AstraIG1/ig1_ztip_elimination.txt` L140–L186: "The crosscut form of
Jordan separation gives two exterior faces"; supplement R.3, `source/spec/p433-480.md` L957: "Jordan
separation gives the stated containment"; the current-face geometry of §5.4, L976).

Three arcs `A_u, A_v, A_w ⊆ ℂ` from `a` to `b` that meet only at `a` and `b` form a θ-curve
`Θ = A_u ∪ A_v ∪ A_w`. Each union of two of them is a Jordan curve `C_{uv} = A_u ∪ A_v`, etc.

## Main results

The inside `jordanIn J` and outside `jordanOut J` of a Jordan curve and their API are reused from
`WangWu/ChamberJordan.lean` (PROVE-WW-B4). `WangWu/ChamberTheta.lean` proves the special case of a
crosscut of the unit disc; this file treats three arbitrary arcs.

* `connectedComponentIn_eq_jordanIn`, `subset_jordanIn_or_subset_jordanOut`, … : adapters;
* `exists_arcInt_subset_jordanIn`: the open part of one of the three arcs lies inside the
  Jordan curve formed by the other two;
* `arcInt_subset_jordanOut`: if `A_w°` is inside `C_{uv}`, then `A_v°` is outside `C_{uw}`;
* `compl_theta_subset`: every point off `Θ` lies outside `C_{uv}` or inside `C_{uw}` or `C_{vw}`
  (for every labelling);
* **`theta_curve`** (the θ-curve theorem): if `A_w°` is inside `C_{uv}`, then
  `Θᶜ = outside C_{uv} ⊔ inside C_{uw} ⊔ inside C_{vw}`, the three faces are pairwise disjoint,
  each is the connected component of `Θᶜ` of each of its points, and their frontiers are `C_{uv}`,
  `C_{uw}`, `C_{vw}`;
* **`jordanIn_diff_arc`** (crosscut form): a crosscut `A_w` of the Jordan domain `inside C_{uv}`
  splits it into exactly the two faces `inside C_{uw}` and `inside C_{vw}`.

## Proof

For a connected set `S` off a Jordan curve `C`, `S` lies on one side of `C`; if `S` is unbounded it
is outside. The open arc `A_w°` misses `C_{uv}`, so it is inside or outside. If `A_w°` is inside
`C_{uv}`, the unbounded set `outside C_{uv}` misses `C_{uw}`, so it lies outside `C_{uw}`; every
point of `A_v° ⊆ frontier (outside C_{uv})` is then in `closure (outside C_{uw}) \ C_{uw}`, i.e.
outside `C_{uw}`. If no open arc were inside the other two, each `inside C_{uv}` would lie outside
both `C_{uw}` and `C_{vw}`; Janiszewski's theorem (`C_{uw} ∩ C_{vw} = A_w` is connected) joins it to
a far point off `Θ`, hence off `C_{uv}` — impossible for a bounded component. The same argument shows
that every point of `inside C_{uv} \ A_w` lies inside `C_{uw}` or `C_{vw}`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bornology Topology

namespace InteractingSLE.Foundations.ThetaCurve

/-! ### The two sides of a Jordan curve

The inside `jordanIn J` and the outside `jordanOut J` and their Jordan curve API are those of
`InteractingSLE.WangWu` (`WangWu/ChamberJordan.lean`, PROVE-WW-B4). The adapters below add the
component, cover and closure facts used here. -/

open LQGMetric.JordanMap (IsJordanCurve)
open WangWu (jordanIn jordanOut)

section JordanSides

variable {J : Set ℂ}

theorem mem_jordanIn_or_mem_jordanOut {z : ℂ} (hz : z ∉ J) : z ∈ jordanIn J ∨ z ∈ jordanOut J := by
  have : z ∈ Jᶜ := hz
  rw [WangWu.compl_eq_jordanIn_union_jordanOut] at this
  exact this

theorem mem_jordanIn_of_not_mem_jordanOut {z : ℂ} (hz : z ∉ J) (hzo : z ∉ jordanOut J) :
    z ∈ jordanIn J :=
  (mem_jordanIn_or_mem_jordanOut hz).resolve_right hzo

theorem mem_jordanOut_of_not_mem_jordanIn {z : ℂ} (hz : z ∉ J) (hzi : z ∉ jordanIn J) :
    z ∈ jordanOut J :=
  (mem_jordanIn_or_mem_jordanOut hz).resolve_left hzi

variable (hJ : IsJordanCurve J)
include hJ

theorem closure_jordanOut : closure (jordanOut J) = jordanOut J ∪ J := by
  rw [closure_eq_self_union_frontier, WangWu.frontier_jordanOut hJ]

/-- A preconnected set off a Jordan curve lies on one side (`S ⊆ Jᶜ` form). -/
theorem subset_jordanIn_or_subset_jordanOut {S : Set ℂ} (hS : IsPreconnected S) (hSJ : S ⊆ Jᶜ) :
    S ⊆ jordanIn J ∨ S ⊆ jordanOut J :=
  WangWu.IsPreconnected.subset_jordanIn_or_subset_jordanOut hJ hS
    (Set.subset_compl_iff_disjoint_right.1 hSJ)

omit hJ in
/-- A preconnected unbounded set off a Jordan curve lies outside (`S ⊆ Jᶜ` form). -/
theorem subset_jordanOut_of_not_isBounded {S : Set ℂ} (hS : IsPreconnected S) (hSJ : S ⊆ Jᶜ)
    (hSb : ¬ IsBounded S) : S ⊆ jordanOut J :=
  WangWu.subset_jordanOut_of_isPreconnected hS hSb (Set.subset_compl_iff_disjoint_right.1 hSJ)

/-- The inside of a Jordan curve is the connected component in `Jᶜ` of each of its points. -/
theorem connectedComponentIn_eq_jordanIn {z : ℂ} (hz : z ∈ jordanIn J) :
    connectedComponentIn Jᶜ z = jordanIn J := by
  refine Subset.antisymm ?_ ((WangWu.isPreconnected_jordanIn hJ).subset_connectedComponentIn hz
    (WangWu.jordanIn_subset_compl J))
  exact WangWu.IsPreconnected.subset_jordanIn hJ isPreconnected_connectedComponentIn
    (Set.subset_compl_iff_disjoint_right.1 (connectedComponentIn_subset _ _))
    ⟨z, mem_connectedComponentIn hz.1, hz⟩

/-- The outside of a Jordan curve is the connected component in `Jᶜ` of each of its points. -/
theorem connectedComponentIn_eq_jordanOut {z : ℂ} (hz : z ∈ jordanOut J) :
    connectedComponentIn Jᶜ z = jordanOut J := by
  refine Subset.antisymm ?_ ((WangWu.isPreconnected_jordanOut hJ).subset_connectedComponentIn hz
    (WangWu.jordanOut_subset_compl J))
  exact WangWu.IsPreconnected.subset_jordanOut hJ isPreconnected_connectedComponentIn
    (Set.subset_compl_iff_disjoint_right.1 (connectedComponentIn_subset _ _))
    ⟨z, mem_connectedComponentIn hz.1, hz⟩

/-- A point of `J` off a second Jordan curve `J'`, inside which the inside of `J` lies, is inside
`J'`. -/
theorem mem_jordanIn_of_mem {J' : Set ℂ} (hJ' : IsJordanCurve J') {z : ℂ} (hz : z ∈ J)
    (hzJ' : z ∉ J') (hsub : jordanIn J ⊆ jordanIn J') : z ∈ jordanIn J' := by
  have h2 := closure_mono hsub (WangWu.mem_closure_jordanIn hJ hz)
  rw [WangWu.closure_jordanIn hJ'] at h2
  exact h2.resolve_right hzJ'

/-- If the inside of `J` lies off a second Jordan curve `J'` and some point of `J` is outside `J'`,
then the inside of `J` lies outside `J'`. -/
theorem jordanIn_subset_jordanOut {J' : Set ℂ} (hJ' : IsJordanCurve J') (hsub : jordanIn J ⊆ J'ᶜ)
    {p : ℂ} (hp : p ∈ J) (hpo : p ∈ jordanOut J') : jordanIn J ⊆ jordanOut J' := by
  rcases subset_jordanIn_or_subset_jordanOut hJ' (WangWu.isPreconnected_jordanIn hJ) hsub with h | h
  · exact absurd (mem_jordanIn_of_mem hJ hJ' hp hpo.1 h)
      (Set.disjoint_right.1 (WangWu.disjoint_jordanIn_jordanOut J') hpo)
  · exact h

end JordanSides

/-! ### Arcs -/

/-- `γ` parametrizes an **arc from `a` to `b`** on `[0, 1]`: continuous and injective there, with
`γ 0 = a` and `γ 1 = b`. -/
def IsArcFrom (γ : ℝ → ℂ) (a b : ℂ) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ γ 0 = a ∧ γ 1 = b

/-- The arc `γ([0, 1])`. -/
abbrev arc (γ : ℝ → ℂ) : Set ℂ := γ '' Icc 0 1

/-- The open part `γ((0, 1))` of an arc. -/
def arcInt (γ : ℝ → ℂ) : Set ℂ := γ '' Ioo 0 1

section Arcs

variable {γ : ℝ → ℂ} {a b : ℂ}

theorem IsArcFrom.ne (h : IsArcFrom γ a b) : a ≠ b := fun hab =>
  zero_ne_one (h.2.1 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    (h.2.2.1.trans (hab.trans h.2.2.2.symm)))

theorem IsArcFrom.left_mem (h : IsArcFrom γ a b) : a ∈ arc γ :=
  ⟨0, left_mem_Icc.2 zero_le_one, h.2.2.1⟩

theorem IsArcFrom.right_mem (h : IsArcFrom γ a b) : b ∈ arc γ :=
  ⟨1, right_mem_Icc.2 zero_le_one, h.2.2.2⟩

theorem IsArcFrom.isCompact (h : IsArcFrom γ a b) : IsCompact (arc γ) :=
  isCompact_Icc.image_of_continuousOn h.1

theorem IsArcFrom.isPreconnected (h : IsArcFrom γ a b) : IsPreconnected (arc γ) :=
  isPreconnected_Icc.image γ h.1

theorem arcInt_subset_arc : arcInt γ ⊆ arc γ := image_mono Ioo_subset_Icc_self

theorem IsArcFrom.isPreconnected_arcInt (h : IsArcFrom γ a b) : IsPreconnected (arcInt γ) :=
  isPreconnected_Ioo.image γ (h.1.mono Ioo_subset_Icc_self)

theorem nonempty_arcInt : (arcInt γ).Nonempty :=
  ⟨γ (1 / 2), 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem IsArcFrom.left_not_mem_arcInt (h : IsArcFrom γ a b) : a ∉ arcInt γ := by
  rintro ⟨t, ht, hta⟩
  have := h.2.1 (Ioo_subset_Icc_self ht) (left_mem_Icc.2 zero_le_one) (hta.trans h.2.2.1.symm)
  exact ht.1.ne' this

theorem IsArcFrom.right_not_mem_arcInt (h : IsArcFrom γ a b) : b ∉ arcInt γ := by
  rintro ⟨t, ht, htb⟩
  have := h.2.1 (Ioo_subset_Icc_self ht) (right_mem_Icc.2 zero_le_one) (htb.trans h.2.2.2.symm)
  exact ht.2.ne this

/-- A point of an arc is an interior point or an endpoint. -/
theorem IsArcFrom.mem_arc (h : IsArcFrom γ a b) {z : ℂ} (hz : z ∈ arc γ) :
    z ∈ arcInt γ ∨ z = a ∨ z = b := by
  obtain ⟨t, ht, rfl⟩ := hz
  rcases ht.1.eq_or_lt with h0 | h0
  · exact Or.inr (Or.inl (by rw [← h0]; exact h.2.2.1))
  rcases ht.2.eq_or_lt with h1 | h1
  · exact Or.inr (Or.inr (by rw [h1]; exact h.2.2.2))
  · exact Or.inl ⟨t, ⟨h0, h1⟩, rfl⟩

/-- The open part of an arc misses any set meeting the arc only at its endpoints. -/
theorem IsArcFrom.disjoint_arcInt (h : IsArcFrom γ a b) {S : Set ℂ} (hS : arc γ ∩ S ⊆ {a, b}) :
    Disjoint (arcInt γ) S := by
  refine Set.disjoint_left.2 fun z hz hzS => ?_
  rcases hS ⟨arcInt_subset_arc hz, hzS⟩ with rfl | rfl
  · exact h.left_not_mem_arcInt hz
  · exact h.right_not_mem_arcInt hz

end Arcs

/-- Two arcs from `a` to `b` meeting only at `a, b` form a Jordan curve. -/
theorem isJordanCurve_arc_union {u v : ℝ → ℂ} {a b : ℂ} (hu : IsArcFrom u a b)
    (hv : IsArcFrom v a b) (huv : arc u ∩ arc v ⊆ {a, b}) : IsJordanCurve (arc u ∪ arc v) :=
  Sec7.isJordanCurve_image_union hu.1 hv.1 hu.2.1 hv.2.1 (hu.2.2.1.trans hv.2.2.1.symm)
    (hu.2.2.2.trans hv.2.2.2.symm) (by rw [hu.2.2.1, hu.2.2.2]; exact huv)

/-- Finitely many bounded sets have a common far point on an unbounded preconnected set off them:
a point lying outside each of three Jordan curves. -/
theorem exists_mem_jordanOut₃ {C₁ C₂ C₃ : Set ℂ} (h₁ : IsJordanCurve C₁)
    (h₂ : IsJordanCurve C₂) (h₃ : IsJordanCurve C₃) :
    ∃ y, y ∈ jordanOut C₁ ∧ y ∈ jordanOut C₂ ∧ y ∈ jordanOut C₃ := by
  have hK : IsBounded (C₁ ∪ C₂ ∪ C₃) :=
    ((WangWu.isCompact_of_isJordanCurve' h₁).isBounded.union
      (WangWu.isCompact_of_isJordanCurve' h₂).isBounded).union (WangWu.isCompact_of_isJordanCurve' h₃).isBounded
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  set S : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ici (|R| + 1) with hS
  have hSp : IsPreconnected S := isPreconnected_Ici.image _ Complex.continuous_ofReal.continuousOn
  have hnorm : ∀ z ∈ S, |R| + 1 ≤ ‖z‖ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ht.trans (le_abs_self t)
  have hSK : S ⊆ (C₁ ∪ C₂ ∪ C₃)ᶜ := fun z hz hzK => by
    have h1 := hR hzK
    rw [mem_closedBall, dist_zero_right] at h1
    have := hnorm z hz
    linarith [le_abs_self R]
  have hSb : ¬ IsBounded S := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    have hmem : ((max (|R| + 1) (|M| + 1) : ℝ) : ℂ) ∈ S := ⟨_, mem_Ici.2 (le_max_left _ _), rfl⟩
    have h1 := hM hmem
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 : |M| + 1 ≤ max (|R| + 1) (|M| + 1) := le_max_right _ _
    have h3 : max (|R| + 1) (|M| + 1) ≤ |max (|R| + 1) (|M| + 1)| := le_abs_self _
    linarith [le_abs_self M]
  have hyS : ((|R| + 1 : ℝ) : ℂ) ∈ S := ⟨_, mem_Ici.2 le_rfl, rfl⟩
  refine ⟨((|R| + 1 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · exact subset_jordanOut_of_not_isBounded hSp
      (hSK.trans (compl_subset_compl.2 (subset_union_left.trans subset_union_left))) hSb hyS
  · exact subset_jordanOut_of_not_isBounded hSp
      (hSK.trans (compl_subset_compl.2 (subset_union_right.trans subset_union_left))) hSb hyS
  · exact subset_jordanOut_of_not_isBounded hSp
      (hSK.trans (compl_subset_compl.2 subset_union_right)) hSb hyS

/-! ### θ-curves -/

section Theta

variable {u v w : ℝ → ℂ} {a b : ℂ}

/-- The open part of the arc `w` misses the Jordan curve `C_{uv}`. -/
theorem arcInt_subset_compl_union (hw : IsArcFrom w a b) (huw : arc u ∩ arc w ⊆ {a, b})
    (hvw : arc v ∩ arc w ⊆ {a, b}) : arcInt w ⊆ (arc u ∪ arc v)ᶜ := by
  intro z hz hzC
  rcases hzC with h | h
  · exact Set.disjoint_left.1 (hw.disjoint_arcInt (by rw [inter_comm]; exact huw)) hz h
  · exact Set.disjoint_left.1 (hw.disjoint_arcInt (by rw [inter_comm]; exact hvw)) hz h

/-- `C_{uw} ∩ C_{vw} = A_w`. -/
theorem union_inter_union_eq (hw : IsArcFrom w a b) (huv : arc u ∩ arc v ⊆ {a, b}) :
    (arc u ∪ arc w) ∩ (arc v ∪ arc w) = arc w := by
  refine Subset.antisymm ?_ fun z hz => ⟨Or.inr hz, Or.inr hz⟩
  rintro z ⟨h₁ | h₁, h₂ | h₂⟩
  · rcases huv ⟨h₁, h₂⟩ with rfl | rfl
    · exact hw.left_mem
    · exact hw.right_mem
  all_goals assumption

/-- **The Janiszewski step.** A point off the θ-curve that lies outside both `C_{uw}` and
`C_{vw}` is not inside `C_{uv}`. -/
theorem not_mem_jordanIn_of_mem_jordanOut (hu : IsArcFrom u a b) (hv : IsArcFrom v a b)
    (hw : IsArcFrom w a b) (huv : arc u ∩ arc v ⊆ {a, b}) (huw : arc u ∩ arc w ⊆ {a, b})
    (hvw : arc v ∩ arc w ⊆ {a, b}) {z : ℂ} (hzΘ : z ∉ arc u ∪ arc v ∪ arc w)
    (h₁ : z ∈ jordanOut (arc u ∪ arc w)) (h₂ : z ∈ jordanOut (arc v ∪ arc w)) :
    z ∉ jordanIn (arc u ∪ arc v) := by
  intro hz
  have hJuv := isJordanCurve_arc_union hu hv huv
  have hJuw := isJordanCurve_arc_union hu hw huw
  have hJvw := isJordanCurve_arc_union hv hw hvw
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := exists_mem_jordanOut₃ hJuv hJuw hJvw
  have hΘ : (arc u ∪ arc w) ∪ (arc v ∪ arc w) = arc u ∪ arc v ∪ arc w := by
    ext x; simp only [mem_union]; tauto
  have hyΘ : y ∉ (arc u ∪ arc w) ∪ (arc v ∪ arc w) := by
    rintro (h | h)
    · exact hy₂.1 h
    · exact hy₃.1 h
  have hzΘ' : z ∉ (arc u ∪ arc w) ∪ (arc v ∪ arc w) := by rw [hΘ]; exact hzΘ
  have hj := QuantumZipper.CA.Topo.janiszewski (WangWu.isCompact_of_isJordanCurve' hJuw)
    (WangWu.isCompact_of_isJordanCurve' hJvw)
    (by rw [union_inter_union_eq hw huv]; exact hw.isPreconnected) hzΘ' hyΘ
    (by rw [connectedComponentIn_eq_jordanOut hJuw h₁]; exact hy₂)
    (by rw [connectedComponentIn_eq_jordanOut hJvw h₂]; exact hy₃)
  rw [hΘ] at hj
  have hmono : connectedComponentIn (arc u ∪ arc v ∪ arc w)ᶜ z ⊆
      connectedComponentIn (arc u ∪ arc v)ᶜ z :=
    connectedComponentIn_mono _ (compl_subset_compl.2 subset_union_left)
  have hyin := hmono hj
  rw [connectedComponentIn_eq_jordanIn hJuv hz] at hyin
  exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut _) hyin hy₁

/-- **The outer arc.** If the open arc `A_w°` is inside `C_{uv}`, then `A_v°` is outside
`C_{uw}`. -/
theorem arcInt_subset_jordanOut (hu : IsArcFrom u a b) (hv : IsArcFrom v a b)
    (hw : IsArcFrom w a b) (huv : arc u ∩ arc v ⊆ {a, b}) (huw : arc u ∩ arc w ⊆ {a, b})
    (hvw : arc v ∩ arc w ⊆ {a, b}) (hin : arcInt w ⊆ jordanIn (arc u ∪ arc v)) :
    arcInt v ⊆ jordanOut (arc u ∪ arc w) := by
  have hJuv := isJordanCurve_arc_union hu hv huv
  have hJuw := isJordanCurve_arc_union hu hw huw
  have h1 : jordanOut (arc u ∪ arc v) ⊆ (arc u ∪ arc w)ᶜ := by
    intro z hz hzC
    rcases hzC with h | h
    · exact hz.1 (Or.inl h)
    · rcases hw.mem_arc h with h' | rfl | rfl
      · exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut _) (hin h') hz
      · exact hz.1 (Or.inl hu.left_mem)
      · exact hz.1 (Or.inl hu.right_mem)
  have h2 : jordanOut (arc u ∪ arc v) ⊆ jordanOut (arc u ∪ arc w) :=
    subset_jordanOut_of_not_isBounded (WangWu.isPreconnected_jordanOut hJuv) h1
      (WangWu.JordanSides hJuv).2.2.2.2.2.2.1
  intro p hp
  have hpC : p ∈ closure (jordanOut (arc u ∪ arc v)) := by
    rw [closure_jordanOut hJuv]; exact Or.inr (Or.inr (arcInt_subset_arc hp))
  have h3 := closure_mono h2 hpC
  rw [closure_jordanOut hJuw] at h3
  exact h3.resolve_right (arcInt_subset_compl_union hv huv (by rw [inter_comm]; exact hvw) hp)

/-- **One arc lies inside the other two.** For a θ-curve, the open part of one of the three arcs
lies inside the Jordan curve formed by the other two. -/
theorem exists_arcInt_subset_jordanIn (hu : IsArcFrom u a b) (hv : IsArcFrom v a b)
    (hw : IsArcFrom w a b) (huv : arc u ∩ arc v ⊆ {a, b}) (huw : arc u ∩ arc w ⊆ {a, b})
    (hvw : arc v ∩ arc w ⊆ {a, b}) :
    arcInt w ⊆ jordanIn (arc u ∪ arc v) ∨ arcInt u ⊆ jordanIn (arc v ∪ arc w) ∨
      arcInt v ⊆ jordanIn (arc u ∪ arc w) := by
  have hJuv := isJordanCurve_arc_union hu hv huv
  have hJuw := isJordanCurve_arc_union hu hw huw
  have hJvw := isJordanCurve_arc_union hv hw hvw
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hw', hu', hv'⟩ := hcon
  have hwo : arcInt w ⊆ jordanOut (arc u ∪ arc v) :=
    (subset_jordanIn_or_subset_jordanOut hJuv hw.isPreconnected_arcInt
      (arcInt_subset_compl_union hw huw hvw)).resolve_left hw'
  have huo : arcInt u ⊆ jordanOut (arc v ∪ arc w) :=
    (subset_jordanIn_or_subset_jordanOut hJvw hu.isPreconnected_arcInt
      (arcInt_subset_compl_union hu (by rw [inter_comm]; exact huv)
        (by rw [inter_comm]; exact huw))).resolve_left hu'
  have hvo : arcInt v ⊆ jordanOut (arc u ∪ arc w) :=
    (subset_jordanIn_or_subset_jordanOut hJuw hv.isPreconnected_arcInt
      (arcInt_subset_compl_union hv huv (by rw [inter_comm]; exact hvw))).resolve_left hv'
  -- the inside of `C_{uv}` misses `A_w`, hence lies off the θ-curve
  have hinΘ : ∀ z ∈ jordanIn (arc u ∪ arc v), z ∉ arc w := by
    intro z hz h
    rcases hw.mem_arc h with h' | rfl | rfl
    · exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut _) hz (hwo h')
    · exact hz.1 (Or.inl hu.left_mem)
    · exact hz.1 (Or.inl hu.right_mem)
  have hsub₁ : jordanIn (arc u ∪ arc v) ⊆ (arc u ∪ arc w)ᶜ := by
    rintro z hz (h | h)
    · exact hz.1 (Or.inl h)
    · exact hinΘ z hz h
  have hsub₂ : jordanIn (arc u ∪ arc v) ⊆ (arc v ∪ arc w)ᶜ := by
    rintro z hz (h | h)
    · exact hz.1 (Or.inr h)
    · exact hinΘ z hz h
  obtain ⟨p, hp⟩ := (nonempty_arcInt : (arcInt v).Nonempty)
  obtain ⟨q, hq⟩ := (nonempty_arcInt : (arcInt u).Nonempty)
  have ho₁ := jordanIn_subset_jordanOut hJuv hJuw hsub₁
    (Or.inr (arcInt_subset_arc hp)) (hvo hp)
  have ho₂ := jordanIn_subset_jordanOut hJuv hJvw hsub₂
    (Or.inl (arcInt_subset_arc hq)) (huo hq)
  obtain ⟨z, hz⟩ := (WangWu.JordanSides hJuv).2.2.2.1
  refine not_mem_jordanIn_of_mem_jordanOut hu hv hw huv huw hvw ?_ (ho₁ hz) (ho₂ hz) hz
  rintro ((h | h) | h)
  · exact hz.1 (Or.inl h)
  · exact hz.1 (Or.inr h)
  · exact hinΘ z hz h

/-- A preconnected set off `Θ ⊇ C` which is a component of `Cᶜ` is a component of `Θᶜ`. -/
theorem connectedComponentIn_eq_of_subset {Θ C S : Set ℂ} (hS : IsPreconnected S) (hSΘ : S ⊆ Θᶜ)
    (hCΘ : C ⊆ Θ) {z : ℂ} (hz : z ∈ S) (hcomp : connectedComponentIn Cᶜ z = S) :
    connectedComponentIn Θᶜ z = S :=
  Subset.antisymm ((connectedComponentIn_mono _ (compl_subset_compl.2 hCΘ)).trans hcomp.le)
    (hS.subset_connectedComponentIn hz hSΘ)

section Decomposition

variable (hu : IsArcFrom u a b) (hv : IsArcFrom v a b) (hw : IsArcFrom w a b)
  (huv : arc u ∩ arc v ⊆ {a, b}) (huw : arc u ∩ arc w ⊆ {a, b}) (hvw : arc v ∩ arc w ⊆ {a, b})
  (hin : arcInt w ⊆ jordanIn (arc u ∪ arc v))
include hu hv hw huv huw hvw hin

/-- The face `inside C_{uw}` misses the θ-curve. -/
theorem jordanIn_left_subset_compl : jordanIn (arc u ∪ arc w) ⊆ (arc u ∪ arc v ∪ arc w)ᶜ := by
  have hvo := arcInt_subset_jordanOut hu hv hw huv huw hvw hin
  rintro z hz ((h | h) | h)
  · exact hz.1 (Or.inl h)
  · rcases hv.mem_arc h with h' | rfl | rfl
    · exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut _) hz (hvo h')
    · exact hz.1 (Or.inl hu.left_mem)
    · exact hz.1 (Or.inl hu.right_mem)
  · exact hz.1 (Or.inr h)

/-- The face `inside C_{vw}` misses the θ-curve. -/
theorem jordanIn_right_subset_compl :
    jordanIn (arc v ∪ arc w) ⊆ (arc u ∪ arc v ∪ arc w)ᶜ := by
  have := jordanIn_left_subset_compl hv hu hw (by rw [inter_comm]; exact huv) hvw huw
    (by rw [union_comm]; exact hin)
  rwa [union_comm (arc v) (arc u)] at this

/-- The outer face `outside C_{uv}` misses the θ-curve. -/
theorem jordanOut_subset_compl_theta :
    jordanOut (arc u ∪ arc v) ⊆ (arc u ∪ arc v ∪ arc w)ᶜ := by
  rintro z hz ((h | h) | h)
  · exact hz.1 (Or.inl h)
  · exact hz.1 (Or.inr h)
  · rcases hw.mem_arc h with h' | rfl | rfl
    · exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut _) (hin h') hz
    · exact hz.1 (Or.inl hu.left_mem)
    · exact hz.1 (Or.inl hu.right_mem)

omit hin in
/-- Every point off the θ-curve lies in one of the three faces (this holds for every labelling). -/
theorem compl_theta_subset : (arc u ∪ arc v ∪ arc w)ᶜ ⊆
    jordanOut (arc u ∪ arc v) ∪ jordanIn (arc u ∪ arc w) ∪ jordanIn (arc v ∪ arc w) := by
  intro z hz
  have hzuv : z ∉ arc u ∪ arc v := fun h => hz (Or.inl h)
  have hzuw : z ∉ arc u ∪ arc w := by
    rintro (h | h)
    · exact hz (Or.inl (Or.inl h))
    · exact hz (Or.inr h)
  have hzvw : z ∉ arc v ∪ arc w := by
    rintro (h | h)
    · exact hz (Or.inl (Or.inr h))
    · exact hz (Or.inr h)
  by_cases ho : z ∈ jordanOut (arc u ∪ arc v)
  · exact Or.inl (Or.inl ho)
  have hi := mem_jordanIn_of_not_mem_jordanOut hzuv ho
  by_cases h₁ : z ∈ jordanIn (arc u ∪ arc w)
  · exact Or.inl (Or.inr h₁)
  by_cases h₂ : z ∈ jordanIn (arc v ∪ arc w)
  · exact Or.inr h₂
  exact absurd hi (not_mem_jordanIn_of_mem_jordanOut hu hv hw huv huw hvw hz
    (mem_jordanOut_of_not_mem_jordanIn hzuw h₁)
    (mem_jordanOut_of_not_mem_jordanIn hzvw h₂))

theorem connectedComponentIn_theta_eq_jordanOut {z : ℂ}
    (hz : z ∈ jordanOut (arc u ∪ arc v)) :
    connectedComponentIn (arc u ∪ arc v ∪ arc w)ᶜ z = jordanOut (arc u ∪ arc v) :=
  connectedComponentIn_eq_of_subset (WangWu.isPreconnected_jordanOut (isJordanCurve_arc_union hu hv huv))
    (jordanOut_subset_compl_theta hu hv hw huv huw hvw hin) subset_union_left hz
    (connectedComponentIn_eq_jordanOut (isJordanCurve_arc_union hu hv huv) hz)

theorem connectedComponentIn_theta_eq_jordanIn_left {z : ℂ}
    (hz : z ∈ jordanIn (arc u ∪ arc w)) :
    connectedComponentIn (arc u ∪ arc v ∪ arc w)ᶜ z = jordanIn (arc u ∪ arc w) :=
  connectedComponentIn_eq_of_subset (WangWu.isPreconnected_jordanIn (isJordanCurve_arc_union hu hw huw))
    (jordanIn_left_subset_compl hu hv hw huv huw hvw hin)
    (union_subset (subset_union_left.trans subset_union_left) subset_union_right) hz
    (connectedComponentIn_eq_jordanIn (isJordanCurve_arc_union hu hw huw) hz)

theorem connectedComponentIn_theta_eq_jordanIn_right {z : ℂ}
    (hz : z ∈ jordanIn (arc v ∪ arc w)) :
    connectedComponentIn (arc u ∪ arc v ∪ arc w)ᶜ z = jordanIn (arc v ∪ arc w) :=
  connectedComponentIn_eq_of_subset (WangWu.isPreconnected_jordanIn (isJordanCurve_arc_union hv hw hvw))
    (jordanIn_right_subset_compl hu hv hw huv huw hvw hin)
    (union_subset (subset_union_right.trans subset_union_left) subset_union_right) hz
    (connectedComponentIn_eq_jordanIn (isJordanCurve_arc_union hv hw hvw) hz)

theorem disjoint_jordanIn_left_right :
    Disjoint (jordanIn (arc u ∪ arc w)) (jordanIn (arc v ∪ arc w)) := by
  refine Set.disjoint_left.2 fun z h₁ h₂ => ?_
  have heq : jordanIn (arc u ∪ arc w) = jordanIn (arc v ∪ arc w) := by
    rw [← connectedComponentIn_theta_eq_jordanIn_left hu hv hw huv huw hvw hin h₁,
      connectedComponentIn_theta_eq_jordanIn_right hu hv hw huv huw hvw hin h₂]
  have hfr := congrArg frontier heq
  rw [WangWu.frontier_jordanIn (isJordanCurve_arc_union hu hw huw),
    WangWu.frontier_jordanIn (isJordanCurve_arc_union hv hw hvw)] at hfr
  obtain ⟨q, hq⟩ := (nonempty_arcInt : (arcInt u).Nonempty)
  have hq' : q ∈ arc v ∪ arc w := hfr ▸ Or.inl (arcInt_subset_arc hq)
  exact arcInt_subset_compl_union hu (by rw [inter_comm]; exact huv)
    (by rw [inter_comm]; exact huw) hq hq'

theorem disjoint_jordanOut_jordanIn_left :
    Disjoint (jordanOut (arc u ∪ arc v)) (jordanIn (arc u ∪ arc w)) := by
  refine Set.disjoint_left.2 fun z h₁ h₂ => ?_
  have heq : jordanOut (arc u ∪ arc v) = jordanIn (arc u ∪ arc w) := by
    rw [← connectedComponentIn_theta_eq_jordanOut hu hv hw huv huw hvw hin h₁,
      connectedComponentIn_theta_eq_jordanIn_left hu hv hw huv huw hvw hin h₂]
  exact (WangWu.JordanSides (isJordanCurve_arc_union hu hv huv)).2.2.2.2.2.2.1
    (heq ▸ WangWu.isBounded_jordanIn (isJordanCurve_arc_union hu hw huw))

theorem disjoint_jordanOut_jordanIn_right :
    Disjoint (jordanOut (arc u ∪ arc v)) (jordanIn (arc v ∪ arc w)) := by
  refine Set.disjoint_left.2 fun z h₁ h₂ => ?_
  have heq : jordanOut (arc u ∪ arc v) = jordanIn (arc v ∪ arc w) := by
    rw [← connectedComponentIn_theta_eq_jordanOut hu hv hw huv huw hvw hin h₁,
      connectedComponentIn_theta_eq_jordanIn_right hu hv hw huv huw hvw hin h₂]
  exact (WangWu.JordanSides (isJordanCurve_arc_union hu hv huv)).2.2.2.2.2.2.1
    (heq ▸ WangWu.isBounded_jordanIn (isJordanCurve_arc_union hv hw hvw))

/-- **Crosscut form of Jordan separation.** The crosscut `A_w` of the Jordan domain
`inside C_{uv}` splits it into the two faces `inside C_{uw}` and `inside C_{vw}`. -/
theorem jordanIn_diff_arc :
    jordanIn (arc u ∪ arc v) \ arc w =
      jordanIn (arc u ∪ arc w) ∪ jordanIn (arc v ∪ arc w) := by
  apply Subset.antisymm
  · rintro z ⟨hz, hzw⟩
    have hzΘ : z ∉ arc u ∪ arc v ∪ arc w := by
      rintro (h | h)
      · exact hz.1 h
      · exact hzw h
    rcases compl_theta_subset hu hv hw huv huw hvw hzΘ with (h | h) | h
    · exact absurd h (Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut _) hz)
    · exact Or.inl h
    · exact Or.inr h
  · have key : ∀ z, z ∉ arc u ∪ arc v ∪ arc w → z ∉ jordanOut (arc u ∪ arc v) →
        z ∈ jordanIn (arc u ∪ arc v) \ arc w := fun z hzΘ hzo =>
      ⟨mem_jordanIn_of_not_mem_jordanOut (fun h => hzΘ (Or.inl h)) hzo,
        fun h => hzΘ (Or.inr h)⟩
    rintro z (h | h)
    · exact key z (jordanIn_left_subset_compl hu hv hw huv huw hvw hin h)
        (Set.disjoint_right.1 (disjoint_jordanOut_jordanIn_left hu hv hw huv huw hvw hin) h)
    · exact key z (jordanIn_right_subset_compl hu hv hw huv huw hvw hin h)
        (Set.disjoint_right.1 (disjoint_jordanOut_jordanIn_right hu hv hw huv huw hvw hin) h)

/-- **The θ-curve theorem.** For three arcs from `a` to `b` meeting only at `a, b`, with `A_w°`
inside `C_{uv}` (one such labelling exists: `exists_arcInt_subset_jordanIn`): the complement of
`Θ = A_u ∪ A_v ∪ A_w` is the union of the three pairwise disjoint faces `outside C_{uv}`,
`inside C_{uw}`, `inside C_{vw}`; each face is the connected component of `Θᶜ` of each of its
points; and the frontiers of the faces are `C_{uv}`, `C_{uw}`, `C_{vw}`. -/
theorem theta_curve :
    (arc u ∪ arc v ∪ arc w)ᶜ =
      jordanOut (arc u ∪ arc v) ∪ jordanIn (arc u ∪ arc w) ∪
        jordanIn (arc v ∪ arc w) ∧
    Disjoint (jordanOut (arc u ∪ arc v)) (jordanIn (arc u ∪ arc w)) ∧
    Disjoint (jordanOut (arc u ∪ arc v)) (jordanIn (arc v ∪ arc w)) ∧
    Disjoint (jordanIn (arc u ∪ arc w)) (jordanIn (arc v ∪ arc w)) ∧
    (∀ z ∈ jordanOut (arc u ∪ arc v),
      connectedComponentIn (arc u ∪ arc v ∪ arc w)ᶜ z = jordanOut (arc u ∪ arc v)) ∧
    (∀ z ∈ jordanIn (arc u ∪ arc w),
      connectedComponentIn (arc u ∪ arc v ∪ arc w)ᶜ z = jordanIn (arc u ∪ arc w)) ∧
    (∀ z ∈ jordanIn (arc v ∪ arc w),
      connectedComponentIn (arc u ∪ arc v ∪ arc w)ᶜ z = jordanIn (arc v ∪ arc w)) ∧
    frontier (jordanOut (arc u ∪ arc v)) = arc u ∪ arc v ∧
    frontier (jordanIn (arc u ∪ arc w)) = arc u ∪ arc w ∧
    frontier (jordanIn (arc v ∪ arc w)) = arc v ∪ arc w := by
  refine ⟨Subset.antisymm (compl_theta_subset hu hv hw huv huw hvw)
      (union_subset (union_subset (jordanOut_subset_compl_theta hu hv hw huv huw hvw hin)
        (jordanIn_left_subset_compl hu hv hw huv huw hvw hin))
        (jordanIn_right_subset_compl hu hv hw huv huw hvw hin)),
    disjoint_jordanOut_jordanIn_left hu hv hw huv huw hvw hin,
    disjoint_jordanOut_jordanIn_right hu hv hw huv huw hvw hin,
    disjoint_jordanIn_left_right hu hv hw huv huw hvw hin,
    fun z hz => connectedComponentIn_theta_eq_jordanOut hu hv hw huv huw hvw hin hz,
    fun z hz => connectedComponentIn_theta_eq_jordanIn_left hu hv hw huv huw hvw hin hz,
    fun z hz => connectedComponentIn_theta_eq_jordanIn_right hu hv hw huv huw hvw hin hz,
    WangWu.frontier_jordanOut (isJordanCurve_arc_union hu hv huv),
    WangWu.frontier_jordanIn (isJordanCurve_arc_union hu hw huw),
    WangWu.frontier_jordanIn (isJordanCurve_arc_union hv hw hvw)⟩

end Decomposition

end Theta

end InteractingSLE.Foundations.ThetaCurve
