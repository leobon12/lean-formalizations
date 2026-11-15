/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoFaceSide
import InteractingSLE.WangWu.PlanarDescent

/-!
# Physical separation by the outer excursion face

One right-side point puts the entire physical outer face on the right, by the
existing planar descent component lemma. Its closure then misses the open left
side, so the counterflow tip is not on the left. A positive real boundary access
or an oriented chart collar supplies the required point. The remaining global
construction is recorded as an explicit hypothesis, with no side conclusion in
its type; the exact original no-wrap statement is assembled conditionally.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

variable {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}

/-- The outer physical face lies in a single component of the proper-arc
complement. A right-side witness therefore orients the whole face. -/
theorem physicalOuterFace_subset_rightSideOf (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (hb : IsBounded (chartFlowSet η w s))
    {z : ℂ} (hz : z ∈ physicalOuterFace η w s)
    (hzR : z ∈ rightSideOf (arcRange η)) :
    physicalOuterFace η w s ⊆ rightSideOf (arcRange η) :=
  Descent.subset_rightSide_of hη (isPreconnected_physicalOuterFace hw hw0 hs hb)
    (fun _ hv => (physicalOuterFace_subset hw hw0 hs hv).1)
    (disjoint_left.2 fun _ hv => (physicalOuterFace_subset hw hw0 hs hv).2) hz hzR

/-- The counterflow tip is in the closure of this face; the open physical left
side is disjoint from the closure of a face lying on the right. -/
theorem tip_notMem_leftSideOf_of_outerFace_right (hη : IsProperArc η)
    (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (hβs : β s ≠ 0) (hb : IsBounded (chartFlowSet η w s))
    (hright : ∃ z ∈ physicalOuterFace η w s, z ∈ rightSideOf (arcRange η)) :
    negInv (β s) ∉ leftSideOf (arcRange η) := by
  obtain ⟨z, hz, hzR⟩ := hright
  have hright := physicalOuterFace_subset_rightSideOf hη hw hw0 hs hb hz hzR
  have hdis := Cond44Ref.disjoint_closure_leftSideOf hη
    (fun v hv hvL => disjoint_left.1 hη.disjoint_leftSideOf_rightSideOf hvL (hright hv))
  exact disjoint_left.1 hdis (tip_mem_closure_physicalOuterFace hβ hw hw0 hs hβs hb)

/-- A physical face approaching a positive real point contains a right-side
point, using the established boundary-side correspondence of a proper arc. -/
theorem exists_rightSide_of_positive_boundary_access (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    {x : ℝ} (hx : 0 < x) (hcl : (x : ℂ) ∈ closure (physicalOuterFace η w s)) :
    ∃ z ∈ physicalOuterFace η w s, z ∈ rightSideOf (arcRange η) := by
  have : (𝓝[physicalOuterFace η w s] (x : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hmono : 𝓝[physicalOuterFace η w s] (x : ℂ) ≤ 𝓝[H] (x : ℂ) :=
    nhdsWithin_mono _ (fun _ hz => (physicalOuterFace_subset hw hw0 hs hz).1)
  have hself : ∀ᶠ z in 𝓝[physicalOuterFace η w s] (x : ℂ),
      z ∈ physicalOuterFace η w s := self_mem_nhdsWithin
  exact (hself.and
    ((Prop411Q.eventually_mem_rightSideOf hη hx).filter_mono hmono)).exists

/-- A collar or a positive-boundary access suffices for physical separation. -/
theorem tip_notMem_leftSideOf_of_outerFace_access (hη : IsProperArc η)
    (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (hβs : β s ≠ 0) (hb : IsBounded (chartFlowSet η w s))
    (haccess : (∃ x : ℝ, 0 < x ∧ (x : ℂ) ∈ closure (physicalOuterFace η w s)) ∨
      Nonempty (OuterFaceCollar η w s)) :
    negInv (β s) ∉ leftSideOf (arcRange η) := by
  apply tip_notMem_leftSideOf_of_outerFace_right hη hβ hw hw0 hs hβs hb
  rcases haccess with hp | hc
  · obtain ⟨x, hx, hcl⟩ := hp
    exact exists_rightSide_of_positive_boundary_access hη hw hw0 hs hx hcl
  · obtain ⟨c⟩ := hc
    obtain ⟨z, hz, hzR⟩ := exists_rightSide_of_outerFaceCollar hη hw hw0 hs c
    exact ⟨revChartInv w s z, ⟨z, hz, rfl⟩, hzR⟩

end InteractingSLE.Sec5.Prop51HTopo
