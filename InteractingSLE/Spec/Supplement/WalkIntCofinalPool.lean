/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCofinalPrefix
import Mathlib.Logic.Encodable.Basic

/-!
# A monotone sequence dominates every member of a directed retained pool

Each side has a countable raw-cofinal subcollection. Directed upper pairs
combine them. The resulting countable cofinal pool is itself directed, so
Mathlib's directed sequence applies without counting the original models.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace InteractingSLE.Theorem14.WalkIntCofinal

open WalkIntFill

/-- A directed collection of actual retained pairs has a countable
subcollection raw-dominating every member of the whole collection. -/
theorem exists_countable_raw_cofinal {ι : Type*} {sR sL : ExplState}
    (P : ι → RetainedPair sR sL) (hdir : Directed (· ⊆ ·) (fun i => (P i).raw)) :
    ∃ S : Set ι, S.Countable ∧ ∀ i, ∃ j ∈ S, (P i).raw ⊆ (P j).raw := by
  obtain ⟨SR, hSR, hR⟩ := exists_countable_prefix_cofinal (fun i => (P i).right)
  obtain ⟨SL, hSL, hL⟩ := exists_countable_prefix_cofinal (fun i => (P i).left)
  choose upper hleft hright using hdir
  refine ⟨image2 upper SR SL, hSR.image2 hSL upper, fun i => ?_⟩
  obtain ⟨j, hj, hij⟩ := hR i
  obtain ⟨k, hk, hik⟩ := hL i
  refine ⟨upper j k, mem_image2.2 ⟨j, hj, k, hk, rfl⟩, ?_⟩
  exact union_subset
    (hij.trans (subset_union_left.trans (hleft j k)))
    (hik.trans (subset_union_right.trans (hright j k)))

/-- One increasing sequence of actual pairs dominates the entire
nonempty directed pool, not merely its boundary collar cover. -/
theorem exists_monotone_raw_cofinal {ι : Type*} [Nonempty ι] {sR sL : ExplState}
    (P : ι → RetainedPair sR sL) (hdir : Directed (· ⊆ ·) (fun i => (P i).raw)) :
    ∃ a : ℕ → ι, Monotone (fun n => (P (a n)).raw) ∧
      ∀ i, ∃ n, (P i).raw ⊆ (P (a n)).raw := by
  obtain ⟨S, hSc, hS⟩ := exists_countable_raw_cofinal P hdir
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀, hj₀, _⟩ := hS i₀
  let : Inhabited S := ⟨⟨j₀, hj₀⟩⟩
  let : Encodable S := hSc.toEncodable
  let F : S → Set ℂ := fun i => (P i.val).raw
  have hdirS : Directed (· ⊆ ·) F := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i.val j.val
    obtain ⟨q, hq, hkq⟩ := hS k
    exact ⟨⟨q, hq⟩, hik.trans hkq, hjk.trans hkq⟩
  let seq : ℕ → S := hdirS.sequence F
  refine ⟨fun n => (seq n).val, hdirS.sequence_mono, fun i => ?_⟩
  obtain ⟨j, hj, hij⟩ := hS i
  exact ⟨Encodable.encode (⟨j, hj⟩ : S) + 1,
    hij.trans (hdirS.le_sequence ⟨j, hj⟩)⟩

end InteractingSLE.Theorem14.WalkIntCofinal
