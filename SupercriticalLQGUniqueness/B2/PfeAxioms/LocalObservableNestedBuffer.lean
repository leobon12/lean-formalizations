import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableCofinalExists

 







set_option autoImplicit false
noncomputable section

open Set Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_outer_buffer_for_open
    {W U : Set ℂ} (hclW : IsCompact (closure W)) (hclWU : closure W ⊆ U)
    (hU : IsOpen U) (hneW : W.Nonempty) :
    ∃ V : Set ℂ, IsOpen V ∧ IsCompact (closure V) ∧
      closure V ⊆ U ∧ closure W ⊆ V ∧
      IsCompact (frontier V) ∧ (frontier V).Nonempty ∧
      Disjoint (closure W) (frontier V) := by
  obtain ⟨V, hVopen, hclWV, hclV, hclVU⟩ :=
    exists_open_compact_closure_buffer hclW hU hclWU
  have hfrontCompact : IsCompact (frontier V) :=
    hclV.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hVne : V.Nonempty := by
    obtain ⟨z, hz⟩ := hneW
    exact ⟨z, hclWV (subset_closure hz)⟩
  have hVproper : V ≠ univ := by
    intro hVu
    have hc : IsCompact (univ : Set ℂ) := by
      simpa [hVu] using hclV
    exact (not_compactSpace_iff.mpr inferInstance) (isCompact_univ_iff.mp hc)
  have hfrontNe : (frontier V).Nonempty :=
    nonempty_frontier_iff.mpr ⟨hVne, hVproper⟩
  have hclWint : closure W ⊆ interior V := by
    simpa [hVopen.interior_eq] using hclWV
  have hdisj : Disjoint (closure W) (frontier V) :=
    disjoint_interior_frontier.mono hclWint (subset_refl _)
  exact ⟨V, hVopen, hclV, hclVU, hclWV,
    hfrontCompact, hfrontNe, hdisj⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
