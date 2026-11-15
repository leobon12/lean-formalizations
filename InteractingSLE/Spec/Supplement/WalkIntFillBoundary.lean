/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFiberChart
import InteractingSLE.Spec.Supplement.WalkLeafChart

/-!
# A physical boundary support determines its filled hull

The filling is monotone and a compact half-plane hull fills itself. For
the reverse inclusion, a complementary component of the raw support cannot
cross the hull frontier. A component on the hull side is therefore bounded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntFill

/-- A compact half-plane hull is the filling of any subset carrying its
whole frontier in H. The raw subset need not be closed or compact. -/
theorem fillH_eq_of_frontier_subset {K Γ : Set ℂ} (hK : IsHPHull K)
    (hΓ : Γ ⊆ K) (hfront : frontier (H \ K) ∩ H ⊆ closure Γ) :
    fillH Γ = K := by
  refine Subset.antisymm ((fillH_mono hΓ).trans_eq hK.fillH_eq) ?_
  intro z hz
  refine ⟨hK.1 hz, ?_⟩
  by_cases hzΓ : z ∈ closure Γ
  · exact Or.inl hzΓ
  right
  let S := connectedComponentIn (H \ closure Γ) z
  have hzS : z ∈ S := mem_connectedComponentIn ⟨hK.1 hz, hzΓ⟩
  have hS : S ⊆ H \ closure Γ := connectedComponentIn_subset _ _
  have hcover : S ⊆ (H \ K) ∪ (closure (H \ K))ᶜ := by
    intro w hw
    by_cases hwcl : w ∈ closure (H \ K)
    · left
      by_contra hwU
      have hwfr : w ∈ frontier (H \ K) := by
        rw [hK.isOpen.frontier_eq]
        exact ⟨hwcl, hwU⟩
      exact (hS hw).2 (hfront ⟨hwfr, (hS hw).1⟩)
    · exact Or.inr hwcl
  have hd : Disjoint (H \ K) (closure (H \ K))ᶜ :=
    Set.disjoint_left.2 fun w hw hnc => hnc (subset_closure hw)
  rcases IsPreconnected.subset_or_subset hK.isOpen isClosed_closure.isOpen_compl
      hd hcover isPreconnected_connectedComponentIn with hU | hOutside
  · exact (hU hzS).2 hz |>.elim
  · apply hK.2.1.subset
    intro w hw
    by_contra hwK
    exact hOutside hw (subset_closure ⟨(hS hw).1, hwK⟩)

open WalkIntCanon

/-- Proper inverse boundary values on a raw support, together with domain
avoidance, identify the model hull as the filling of that support in H. -/
theorem hull_eq_fillH_of_boundaryRange {c : Chart} (M : HullModel c)
    (hc : c.IsConformal) (hproper : GW1P.HasProperBdryExt c) {A : Set ℂ}
    (hboundary : GW1RestartFinal.HasBoundaryRange c A)
    (havoid : Disjoint (c.dom : Set ℂ) A) :
    M.hull = fillH (A ∩ H) := by
  symm
  apply fillH_eq_of_frontier_subset M.isHull
  · intro z hz
    by_contra hzK
    have hzdom : z ∈ c.dom := by
      change z ∈ (c.dom : Set ℂ)
      rw [M.dom_eq]
      exact ⟨hz.2, hzK⟩
    exact Set.disjoint_left.1 havoid hzdom hz.1
  · rintro z ⟨hzfr, hzH⟩
    rw [← M.dom_eq, c.dom.isOpen.frontier_eq] at hzfr
    exact subset_closure ⟨WalkLeaf.mem_of_frontier_dom hc hproper hboundary hzH
      hzfr.1 hzfr.2, hzH⟩

end InteractingSLE.Theorem14.WalkIntFill
