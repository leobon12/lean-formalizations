/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntSelectPrefix
import Mathlib.Topology.Compactness.Lindelof

/-!
# Countably many prefixes dominate any indexed prefix collection

At each recorded instruction position only the own-time parameter varies.
Every collection of nonnegative real times has a countable cofinal subset.
There are only countably many instruction positions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntCofinal

open WalkBdry WalkIntFill

/-- A same-position prefix at a later own time contains the earlier raw set. -/
theorem raw_subset_of_position_time_le {s : ExplState} {P Q : WalkPrefix s}
    (hpos : P.pre.length = Q.pre.length) (ht : P.time ≤ Q.time) : P.raw ⊆ Q.raw := by
  have heq := P.split.symm.trans Q.split
  have hpre : P.pre = Q.pre := List.append_inj_left heq hpos
  have hpc : P.piece = Q.piece := by
    rw [hpre] at heq
    exact (List.cons.inj (List.append_cancel_left heq)).1
  rintro z ⟨hz, hzH⟩
  refine ⟨?_, hzH⟩
  rcases hz with hz | ⟨t, hτ, hlim⟩
  · exact Or.inl (hpre ▸ hz)
  · exact Or.inr ⟨t, hτ.trans (by exact_mod_cast ht), hpc ▸ hlim⟩

/-- Any indexed collection of nonnegative real values has countably
many cofinal witnesses, including its maximum when one exists. -/
theorem exists_countable_time_cofinal {ι : Type*} (f : ι → ℝ≥0) :
    ∃ S : Set ι, S.Countable ∧ ∀ i, ∃ j ∈ S, f i ≤ f j := by
  classical
  by_cases hmax : ∃ i, ∀ j, f j ≤ f i
  · obtain ⟨i, hi⟩ := hmax
    exact ⟨{i}, countable_singleton i, fun j => ⟨i, mem_singleton i, hi j⟩⟩
  · have hgt (i : ι) : ∃ j, f i < f j := by
      by_contra h
      exact hmax ⟨i, fun j => le_of_not_gt (fun hij => h ⟨j, hij⟩)⟩
    have hcover : range f ⊆ ⋃ i, Iio (f i) := by
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hgt i
      exact mem_iUnion.2 ⟨j, hj⟩
    have hL : IsLindelof (range f) := HereditarilyLindelofSpace.isLindelof (range f)
    obtain ⟨S, hS, hcoverS⟩ := hL.elim_countable_subcover
      (fun i => Iio (f i)) (fun _ => isOpen_Iio) hcover
    refine ⟨S, hS, fun i => ?_⟩
    obtain ⟨j, hj, hij⟩ := mem_iUnion₂.1 (hcoverS (mem_range_self i))
    exact ⟨j, hj, le_of_lt hij⟩

/-- A countable subcollection raw-dominates every prefix in an arbitrary
indexed collection. No countability of the original models is assumed. -/
theorem exists_countable_prefix_cofinal {ι : Type*} {s : ExplState}
    (P : ι → WalkPrefix s) :
    ∃ S : Set ι, S.Countable ∧ ∀ i, ∃ j ∈ S, (P i).raw ⊆ (P j).raw := by
  choose S hSc hS using fun n : ℕ => exists_countable_time_cofinal
    (fun i : {i : ι // (P i).pre.length = n} => (P i.val).time)
  let T : Set ι := ⋃ n : ℕ, Subtype.val '' S n
  refine ⟨T, countable_iUnion (fun n => (hSc n).image Subtype.val), fun i => ?_⟩
  obtain ⟨j, hj, ht⟩ := hS (P i).pre.length ⟨i, rfl⟩
  exact ⟨j.val, mem_iUnion.2 ⟨(P i).pre.length, mem_image_of_mem Subtype.val hj⟩,
    raw_subset_of_position_time_le j.property.symm ht⟩

end InteractingSLE.Theorem14.WalkIntCofinal
