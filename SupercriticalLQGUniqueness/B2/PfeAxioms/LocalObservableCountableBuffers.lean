import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableNestedBuffer

 







set_option autoImplicit false
noncomputable section

open Set Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_countable_nested_buffers
    {U : Set ℂ} (hU : IsOpen U) (H : CompactExhaustion U)
    (x y : U) :
    ∃ W V : ℕ → Set ℂ, ∀ n,
      IsOpen (W n) ∧ IsCompact (closure (W n)) ∧
      closure (W n) ⊆ U ∧
      (H n).image Subtype.val ⊆ W n ∧
      (x : ℂ) ∈ W n ∧ (y : ℂ) ∈ W n ∧
      IsOpen (V n) ∧ IsCompact (closure (V n)) ∧
      closure (V n) ⊆ U ∧ closure (W n) ⊆ V n ∧
      IsCompact (frontier (V n)) ∧
      (frontier (V n)).Nonempty ∧
      Disjoint (closure (W n)) (frontier (V n)) := by
  classical
  obtain ⟨W, hW⟩ := exists_countable_open_buffers hU H x y
  have hp : ∀ n : ℕ, ∃ V : Set ℂ,
      IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ U ∧
      closure (W n) ⊆ V ∧ IsCompact (frontier V) ∧
      (frontier V).Nonempty ∧
      Disjoint (closure (W n)) (frontier V) := by
    intro n
    exact exists_outer_buffer_for_open
      (hW n).2.1 (hW n).2.2.1 hU ⟨x, (hW n).2.2.2.2.1⟩
  choose V hVopen hVcompact hVclU hclWV hfrontCompact hfrontNe hdisj using hp
  refine ⟨W, V, fun n => ?_⟩
  exact ⟨(hW n).1, (hW n).2.1, (hW n).2.2.1,
    (hW n).2.2.2.1, (hW n).2.2.2.2.1,
    (hW n).2.2.2.2.2, hVopen n, hVcompact n,
    hVclU n, hclWV n, hfrontCompact n, hfrontNe n,
    hdisj n⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
