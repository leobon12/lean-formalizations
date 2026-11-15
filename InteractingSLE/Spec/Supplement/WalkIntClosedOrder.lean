/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntClosedRetained

/-!
# Chronological comparison with the final recorded piece

Every closed-time prefix lies inside the final-piece prefix at its own
finite time. At an earlier instruction position, the entire piece has
already been included. At the final position the recorded data coincide.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntClosed

open WalkBdry

theorem prefixSet_mono_time (pre : List Piece) (pc : Piece) {a b : ℝ≥0} (h : a ≤ b) :
    prefixSet pre pc a ⊆ prefixSet pre pc b := by
  rintro z ⟨hz | ⟨t, ht, hlim⟩, hzH⟩
  · exact ⟨Or.inl hz, hzH⟩
  · exact ⟨Or.inr ⟨t, ht.trans (by exact_mod_cast h), hlim⟩, hzH⟩

/-- Earlier positions contribute their whole recorded support; at the
last position the earlier-list and piece identities follow by cancellation. -/
theorem ClosedPrefix.raw_subset_last_prefix {s : ExplState} (R : ClosedPrefix s)
    {pre : List Piece} {pc : Piece} (hs : s.1 = pre ++ [pc]) :
    R.raw ⊆ prefixSet pre pc R.time := by
  have heq := R.split.symm.trans hs
  have hlen : R.pre.length ≤ pre.length := by
    have h := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  rcases hlen.lt_or_eq with hlt | he
  · have hp : R.pre ++ [R.piece] <+: s.1 :=
      ⟨R.post, by simpa only [List.append_assoc, List.singleton_append] using R.split.symm⟩
    have hq : pre <+: s.1 := ⟨[pc], hs.symm⟩
    have hpre : R.pre ++ [R.piece] <+: pre :=
      List.prefix_of_prefix_length_le hp hq (by
        simpa only [List.length_append, List.length_singleton] using Nat.succ_le_of_lt hlt)
    rintro z ⟨hz | ⟨t, ht, hlim⟩, hzH⟩
    · obtain ⟨q, hq, hz⟩ := mem_iUnion₂.1 hz
      exact ⟨Or.inl (mem_iUnion₂.2
        ⟨q, hpre.subset (List.mem_append_left _ hq), hz⟩), hzH⟩
    · exact ⟨Or.inl (mem_iUnion₂.2 ⟨R.piece,
        hpre.subset (List.mem_append_right _ (List.mem_singleton_self _)),
        t, ht.trans R.time_le, hlim⟩), hzH⟩
  · have hpre : R.pre = pre := List.append_inj_left heq he
    have hpc : R.piece = pc := by
      rw [hpre] at heq
      exact (List.cons.inj (List.append_cancel_left heq)).1
    rw [ClosedPrefix.raw, hpre, hpc]

end InteractingSLE.Theorem14.WalkIntClosed
