/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFillPrefix

/-!
# The union of retained raw prefixes has a compact half-plane hull

Filling the two prefixes separately before filling their union gives the
same hull. Their interiors cannot contribute a new outer boundary point.
Only the raw ordinary prefix sets need be used as the filling support.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntFill

/-- The filling of the union of two compact half-plane hulls is a compact
half-plane hull. The lower half-plane joins all their components. -/
theorem isHPHull_fillH_union {A B : Set ℂ} (hA : IsHPHull A) (hB : IsHPHull B) :
    IsHPHull (fillH (A ∪ B)) :=
  isHPHull_fillH_of_isPreconnected (hA.2.1.union hB.2.1)
    (isPreconnected_union_lowerHalf hA.isPreconnected_union_lowerHalf
      hB.isPreconnected_union_lowerHalf)

/-- Filling each raw support separately does not change the filled union.
The supports here are the ordinary sets in H, not real connector segments. -/
theorem fillH_union_filled {A B : Set ℂ} (hAH : A ⊆ H) (hBH : B ⊆ H)
    (hA : IsHPHull (fillH A)) (hB : IsHPHull (fillH B)) :
    fillH (fillH A ∪ fillH B) = fillH (A ∪ B) := by
  let K := fillH (fillH A ∪ fillH B)
  have hK : IsHPHull K := isHPHull_fillH_union hA hB
  have hAK : fillH A ⊆ K := fun z hz =>
    mem_fillH_of_mem_closure (hA.1 hz) (subset_closure (Or.inl hz))
  have hBK : fillH B ⊆ K := fun z hz =>
    mem_fillH_of_mem_closure (hB.1 hz) (subset_closure (Or.inr hz))
  symm
  apply fillH_eq_of_frontier_subset hK
  · rintro z (hz | hz)
    · exact hAK (mem_fillH_of_mem_closure (hAH hz) (subset_closure hz))
    · exact hBK (mem_fillH_of_mem_closure (hBH hz) (subset_closure hz))
  · rintro z ⟨hzfr, hzH⟩
    have hzcl : z ∈ closure (H \ K) := frontier_subset_closure hzfr
    have hraw := frontier_H_diff_fillH_subset (hA.2.1.union hB.2.1) hzfr
    rcases hraw with hzero | hcl
    · exact ((ne_of_gt (show 0 < z.im from hzH)) hzero).elim
    rw [closure_union] at hcl
    rcases hcl with hcl | hcl
    · have hzA := hA.mem_of_mem_closure hzH hcl
      have hAc := closure_mono (sdiff_subset_sdiff_right hAK) hzcl
      exact closure_mono subset_union_left
        (mem_closure_of_mem_fillH_of_mem_closure hzA hAc)
    · have hzB := hB.mem_of_mem_closure hzH hcl
      have hBc := closure_mono (sdiff_subset_sdiff_right hBK) hzcl
      exact closure_mono subset_union_right
        (mem_closure_of_mem_fillH_of_mem_closure hzB hBc)

theorem isHPHull_fillH_raw_union {A B : Set ℂ} (hAH : A ⊆ H) (hBH : B ⊆ H)
    (hA : IsHPHull (fillH A)) (hB : IsHPHull (fillH B)) :
    IsHPHull (fillH (A ∪ B)) := by
  rw [← fillH_union_filled hAH hBH hA hB]
  exact isHPHull_fillH_union hA hB

end InteractingSLE.Theorem14.WalkIntFill
