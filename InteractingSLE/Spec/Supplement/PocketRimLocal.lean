/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketRimEndpoints

/-!
# Local identification of components at a crosscut

PROVE-POCKETSHAPE continuation. Reuse the existing Schoenflies neighbourhoods:
two complement components on the same side of a crosscut that approach one point
off the other crosscut coincide. No global order of the walls is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Theorem14.PocketRim

open GW4Reg WangWu Sec7.Lemma71I

/-- A closure point inside the disc and off a crosscut remains on the same side. -/
theorem mem_crossSide_of_mem_closure {α : ℝ → ℂ} (hα : IsDiscCrosscut α)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : ℂ} (hpD : p ∈ ball (0 : ℂ) 1)
    (hpα : p ∉ crossRange α) (hp : p ∈ closure (crossSide α σ)) : p ∈ crossSide α σ := by
  rw [hα.closure_crossSide hσ] at hp
  rcases hp with hp | hp | hp
  · exact hp
  · exact (hpα hp).elim
  · have hlt : ‖p‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hpD
    rw [hp.1] at hlt
    exact (lt_irrefl (1 : ℝ) hlt).elim

/-- Two components on the same upper side approaching a point off the other wall coincide.
This extracts the local Schoenflies step of `WangWu.exists_contactGap_of_between`. -/
theorem component_eq_of_same_side_closure {α β : ℝ → ℂ}
    (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β) {z w p : ℂ}
    (hzside : connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) z ⊆ crossSide α 1)
    (hwside : connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) w ⊆ crossSide α 1)
    (hpz : p ∈ closure (connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) z))
    (hpw : p ∈ closure (connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) w))
    (hpβ : p ∉ crossRange β) :
    connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) z =
      connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) w := by
  let O : Set ℂ := ball 0 1 \ (crossRange α ∪ crossRange β)
  obtain ⟨ε, hε, hεβ⟩ := Metric.isOpen_iff.1 hβ.isCompact_crossRange.isClosed.isOpen_compl p hpβ
  obtain ⟨N, hN, hNε, hNc⟩ := exists_mem_nhds_isPreconnected_inter_jordanIn hα.isJordanCurve_upper p hε
  have hNO : N ∩ crossSide α 1 ⊆ O := by
    rintro v ⟨hvN, hvS⟩
    have hv := hα.crossSide_subset (Or.inl rfl) hvS
    exact ⟨hv.1, fun h => h.elim hv.2 (fun hvβ => hεβ (hNε hvN) hvβ)⟩
  obtain ⟨c, hcN, hcC⟩ := mem_closure_iff_nhds.1 hpz N hN
  obtain ⟨u, huN, huC⟩ := mem_closure_iff_nhds.1 hpw N hN
  have hcV : c ∈ N ∩ crossSide α 1 := ⟨hcN, hzside hcC⟩
  have huV : u ∈ N ∩ crossSide α 1 := ⟨huN, hwside huC⟩
  have hVz : N ∩ crossSide α 1 ⊆ connectedComponentIn O z := by
    rw [connectedComponentIn_eq hcC]
    exact hNc.subset_connectedComponentIn hcV hNO
  have hVw : N ∩ crossSide α 1 ⊆ connectedComponentIn O w := by
    rw [connectedComponentIn_eq huC]
    exact hNc.subset_connectedComponentIn huV hNO
  exact connectedComponentIn_eq_of_mem_of_mem (hVz hcV) (hVw hcV)

/-- A between-component's Cayley image is a disc complement component on the indicated two sides. -/
theorem cayley_between_component {αR αL : ℝ≥0 → ℂ}
    (hR : IsSimpleProper αR) (hL : IsSimpleProper αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) :
    ∃ z : ℂ,
      cayley '' C = connectedComponentIn
        (ball 0 1 \ (crossRange (toDisc (realPath αR)) ∪ crossRange (toDisc (realPath αL)))) z ∧
      cayley '' C ⊆ crossSide (toDisc (realPath αR)) 1 ∩ crossSide (toDisc (realPath αL)) (-1) := by
  have hCa : C ∈ betweenComponents (arcRange (realPath αR)) (arcRange (realPath αL)) := by
    simpa only [arcRange_realPath] using hC
  obtain ⟨z, hz, hzR, hzL, rfl⟩ := hCa
  have hRa := hR.isProperArc
  have hLa := hL.isProperArc
  have hα := hRa.isDiscCrosscut_toDisc
  have hβ := hLa.isDiscCrosscut_toDisc
  have hzα : z ∉ arcRange (realPath αR) := fun h => hz.2 (Or.inl h)
  have hzβ : z ∉ arcRange (realPath αL) := fun h => hz.2 (Or.inr h)
  have hz1 : cayley z ∈ crossSide (toDisc (realPath αR)) 1 := by
    rcases hRa.mem_leftSideOf_or_mem_rightSideOf hz.1 hzα with hl | hr
    · exact (hRa.mem_leftSideOf_iff hz.1).1 hl
    · exact (hzR hr).elim
  have hz2 : cayley z ∈ crossSide (toDisc (realPath αL)) (-1) := by
    rcases hLa.mem_leftSideOf_or_mem_rightSideOf hz.1 hzβ with hl | hr
    · exact (hzL hl).elim
    · exact (hLa.mem_rightSideOf_iff hz.1).1 hr
  rw [image_cayley_connectedComponentIn sdiff_subset hz, image_cayley_H_diff hRa hLa]
  let O : Set ℂ := ball 0 1 \ (crossRange (toDisc (realPath αR)) ∪ crossRange (toDisc (realPath αL)))
  have hzO : cayley z ∈ O := ⟨(hα.crossSide_subset (Or.inl rfl) hz1).1,
    fun h => h.elim (hα.crossSide_subset (Or.inl rfl) hz1).2
      (hβ.crossSide_subset (Or.inr rfl) hz2).2⟩
  refine ⟨cayley z, rfl, subset_inter ?_ ?_⟩
  · exact hα.subset_crossSide_of_isPreconnected (Or.inl rfl) isPreconnected_connectedComponentIn
      (fun w hw => ⟨(connectedComponentIn_subset O _ hw).1,
        fun h => (connectedComponentIn_subset O _ hw).2 (Or.inl h)⟩)
      ⟨cayley z, mem_connectedComponentIn hzO, hz1⟩
  · exact hβ.subset_crossSide_of_isPreconnected (Or.inr rfl) isPreconnected_connectedComponentIn
      (fun w hw => ⟨(connectedComponentIn_subset O _ hw).1,
        fun h => (connectedComponentIn_subset O _ hw).2 (Or.inr h)⟩)
      ⟨cayley z, mem_connectedComponentIn hzO, hz2⟩

end InteractingSLE.Theorem14.PocketRim
