/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntClosedOrder
import InteractingSLE.Spec.Supplement.WalkIntSelectTail

/-!
# Unions of admissible completed-prefix references

Completed prefixes are ordered by recorded position and own time.
Their coordinatewise union is an actual completed-prefix pair. Taking
the later common exit preserves closed-tail separation on both walks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntOrient

open WalkBdry WalkIntClosed

/-- Own-time monotonicity at a fixed recorded instruction position. -/
theorem closed_raw_subset_of_position_time_le {s : ExplState} {P Q : ClosedPrefix s}
    (hpos : P.pre.length = Q.pre.length) (ht : P.time ≤ Q.time) : P.raw ⊆ Q.raw := by
  have heq := P.split.symm.trans Q.split
  have hpre : P.pre = Q.pre := List.append_inj_left heq hpos
  have hpc : P.piece = Q.piece := by
    rw [hpre] at heq
    exact (List.cons.inj (List.append_cancel_left heq)).1
  change prefixSet P.pre P.piece P.time ⊆ prefixSet Q.pre Q.piece Q.time
  rw [hpre, hpc]
  exact prefixSet_mono_time _ _ ht

/-- An earlier recorded piece is entirely retained at a later position. -/
theorem closed_raw_subset_of_position_lt {s : ExplState} (P Q : ClosedPrefix s)
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
      t, ht.trans P.time_le, hlim⟩

/-- Completed prefixes of the same actual recorded state are comparable. -/
theorem closed_raw_total {s : ExplState} (P Q : ClosedPrefix s) :
    P.raw ⊆ Q.raw ∨ Q.raw ⊆ P.raw := by
  rcases lt_trichotomy P.pre.length Q.pre.length with h | h | h
  · exact Or.inl (closed_raw_subset_of_position_lt P Q h)
  · rcases le_total P.time Q.time with ht | ht
    · exact Or.inl (closed_raw_subset_of_position_time_le h ht)
    · exact Or.inr (closed_raw_subset_of_position_time_le h.symm ht)
  · exact Or.inr (closed_raw_subset_of_position_lt Q P h)

/-- Coordinatewise raw unions have an actual normalized completed model. -/
theorem exists_closed_raw_union {sR sL : ExplState} (J K : ClosedPair sR sL) :
    ∃ M : ClosedPair sR sL,
      M.right.raw = J.right.raw ∪ K.right.raw ∧ M.left.raw = J.left.raw ∪ K.left.raw := by
  have hex {s : ExplState} (P Q : ClosedPrefix s) :
      ∃ R : ClosedPrefix s, R.raw = P.raw ∪ Q.raw := by
    rcases closed_raw_total P Q with h | h
    · exact ⟨Q, (union_eq_right.2 h).symm⟩
    · exact ⟨P, (union_eq_left.2 h).symm⟩
  obtain ⟨R, hR⟩ := hex J.right K.right
  obtain ⟨L, hL⟩ := hex J.left K.left
  obtain ⟨M, hMR, hML⟩ := exists_closedPair R L
  exact ⟨M, hMR ▸ hR, hML ▸ hL⟩

/-- The bounded admissible completed pool is directed. No directedness
or parameter-cutoff hypothesis is supplied by the caller. -/
theorem exists_admissible_closed_upper {sR sL : ExplState} (J K : ClosedPair sR sL)
    {C : Set ℂ} {α β : ℝ≥0 → ℂ}
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    (hJ : Bornology.IsBounded C → ∃ s t : ℝ≥0, 0 < s ∧ 0 < t ∧ α s = β t ∧
      Disjoint (closure J.right.raw) (α '' Ici s) ∧
      Disjoint (closure J.left.raw) (β '' Ici t) ∧ α s ∈ closure C)
    (hK : Bornology.IsBounded C → ∃ s t : ℝ≥0, 0 < s ∧ 0 < t ∧ α s = β t ∧
      Disjoint (closure K.right.raw) (α '' Ici s) ∧
      Disjoint (closure K.left.raw) (β '' Ici t) ∧ α s ∈ closure C) :
    ∃ M : ClosedPair sR sL, J.raw ⊆ M.raw ∧ K.raw ⊆ M.raw ∧
      (Bornology.IsBounded C → ∃ s t : ℝ≥0, 0 < s ∧ 0 < t ∧ α s = β t ∧
        Disjoint (closure M.right.raw) (α '' Ici s) ∧
        Disjoint (closure M.left.raw) (β '' Ici t) ∧ α s ∈ closure C) := by
  obtain ⟨M, hR, hL⟩ := exists_closed_raw_union J K
  have hJM : J.raw ⊆ M.raw := union_subset_union
    (hR ▸ subset_union_left) (hL ▸ subset_union_left)
  have hKM : K.raw ⊆ M.raw := union_subset_union
    (hR ▸ subset_union_right) (hL ▸ subset_union_right)
  refine ⟨M, hJM, hKM, fun hb => ?_⟩
  obtain ⟨s, t, hs, ht, hp, hJR, hJL, hC⟩ := hJ hb
  obtain ⟨s', t', hs', ht', hp', hKR, hKL, hC'⟩ := hK hb
  have hunion {a b : ℝ≥0} (hsa : s ≤ a) (hs'a : s' ≤ a)
      (htb : t ≤ b) (ht'b : t' ≤ b) :
      Disjoint (closure M.right.raw) (α '' Ici a) ∧
        Disjoint (closure M.left.raw) (β '' Ici b) := by
    rw [hR, hL, closure_union, closure_union]
    exact ⟨disjoint_union_left.2
      ⟨hJR.mono_right (image_mono (Ici_subset_Ici.2 hsa)),
        hKR.mono_right (image_mono (Ici_subset_Ici.2 hs'a))⟩,
      disjoint_union_left.2
      ⟨hJL.mono_right (image_mono (Ici_subset_Ici.2 htb)),
        hKL.mono_right (image_mono (Ici_subset_Ici.2 ht'b))⟩⟩
  rcases le_total s s' with h | h
  · have htt := WalkIntSelect.common_contact_le horder hp hp' h
    exact ⟨s', t', hs', ht', hp', (hunion h le_rfl htt le_rfl).1,
      (hunion h le_rfl htt le_rfl).2, hC'⟩
  · have htt := WalkIntSelect.common_contact_le horder hp' hp h
    exact ⟨s, t, hs, ht, hp, (hunion le_rfl h le_rfl htt).1,
      (hunion le_rfl h le_rfl htt).2, hC⟩

end InteractingSLE.Theorem14.WalkIntOrient
