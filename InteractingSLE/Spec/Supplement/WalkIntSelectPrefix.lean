/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFillRetained

/-!
# Finite unions of actual recorded prefixes remain actual prefixes

Prefixes of the same recorded walk are ordered by instruction position and
own time. Their raw sets are therefore comparable by inclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntSelect

open WalkBdry WalkIntFill

/-- Every earlier recorded prefix is contained in every later instruction prefix. -/
theorem raw_subset_of_pre_length_lt {s : ExplState} (P Q : WalkPrefix s)
    (h : P.pre.length < Q.pre.length) : P.raw ⊆ Q.raw := by
  have hp : P.pre ++ [P.piece] <+: s.1 :=
    ⟨P.post, by simpa only [List.append_assoc, List.singleton_append] using P.split.symm⟩
  have hq : Q.pre <+: s.1 := ⟨Q.piece :: Q.post, Q.split.symm⟩
  have hpq : P.pre ++ [P.piece] <+: Q.pre :=
    List.prefix_of_prefix_length_le hp hq (by
      simpa only [List.length_append, List.length_singleton] using Nat.succ_le_of_lt h)
  rintro z ⟨hz, hzH⟩
  refine ⟨Or.inl ?_, hzH⟩
  rcases hz with hz | ⟨t, ht, hlim⟩
  · obtain ⟨pc, hpc, hzp⟩ := mem_iUnion₂.1 hz
    exact mem_iUnion₂.2 ⟨pc, hpq.subset (List.mem_append_left _ hpc), hzp⟩
  · exact mem_iUnion₂.2 ⟨P.piece,
      hpq.subset (List.mem_append_right _ (List.mem_singleton_self _)),
      t, ht.trans P.alive.le, hlim⟩

/-- The raw sets of any two live prefixes of the same state are comparable. -/
theorem prefix_raw_total {s : ExplState} (P Q : WalkPrefix s) :
    P.raw ⊆ Q.raw ∨ Q.raw ⊆ P.raw := by
  rcases lt_trichotomy P.pre.length Q.pre.length with h | h | h
  · exact Or.inl (raw_subset_of_pre_length_lt P Q h)
  · have heq := P.split.symm.trans Q.split
    have hpre : P.pre = Q.pre := List.append_inj_left heq h
    have hpc : P.piece = Q.piece := by
      rw [hpre] at heq
      exact (List.cons.inj (List.append_cancel_left heq)).1
    rcases le_total P.time Q.time with ht | ht
    · left
      rintro z ⟨hz, hzH⟩
      refine ⟨?_, hzH⟩
      rcases hz with hz | ⟨t, hτ, hlim⟩
      · exact Or.inl (hpre ▸ hz)
      · exact Or.inr ⟨t, hτ.trans (by exact_mod_cast ht), hpc ▸ hlim⟩
    · right
      rintro z ⟨hz, hzH⟩
      refine ⟨?_, hzH⟩
      rcases hz with hz | ⟨t, hτ, hlim⟩
      · exact Or.inl (hpre.symm ▸ hz)
      · exact Or.inr ⟨t, hτ.trans (by exact_mod_cast ht), hpc.symm ▸ hlim⟩
  · exact Or.inr (raw_subset_of_pre_length_lt Q P h)

/-- Taking a raw union requires selecting one of the two actual prefixes. -/
theorem exists_prefix_raw_union {s : ExplState} (P Q : WalkPrefix s) :
    ∃ R : WalkPrefix s, R.raw = P.raw ∪ Q.raw := by
  rcases prefix_raw_total P Q with h | h
  · exact ⟨Q, (union_eq_right.2 h).symm⟩
  · exact ⟨P, (union_eq_left.2 h).symm⟩

/-- Coordinatewise prefix unions have an actual normalized retained-pair model. -/
theorem exists_retained_raw_union {sR sL : ExplState} (J K : RetainedPair sR sL) :
    ∃ M : RetainedPair sR sL,
      M.right.raw = J.right.raw ∪ K.right.raw ∧
      M.left.raw = J.left.raw ∪ K.left.raw := by
  obtain ⟨R, hR⟩ := exists_prefix_raw_union J.right K.right
  obtain ⟨L, hL⟩ := exists_prefix_raw_union J.left K.left
  obtain ⟨M, hMR, hML⟩ := exists_retainedPair R L
  exact ⟨M, hMR ▸ hR, hML ▸ hL⟩

end InteractingSLE.Theorem14.WalkIntSelect
