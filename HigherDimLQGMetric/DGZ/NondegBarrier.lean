import HigherDimLQGMetric.DGZ.NondegComponents

/-! A compact frontier disjoint from a metric zero set has positive distance to the target shell. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ} {rGrid : ℝ}

theorem nd_frontier_domain_nonempty (hd : 0 < d) (rGrid : ℝ)
    (i : nd_DomainIndex d rGrid) (hU : (nd_domain rGrid i).Nonempty) :
    (frontier (nd_domain rGrid i)).Nonempty := by
  haveI : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  apply nonempty_frontier_iff.mpr
  refine ⟨hU, ?_⟩
  intro heq
  have hb : Bornology.IsBounded (Set.univ : Set (Rd d)) := by
    rw [← heq]
    exact nd_isBounded_domain rGrid i
  exact NormedSpace.unbounded_univ ℝ (Rd d) hb

theorem nd_exists_setInf_eq {A B : Set (Rd d)} (hA : IsCompact A)
    (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (D : C(Rd d × Rd d, ℝ)) :
    ∃ p ∈ A ×ˢ B, nd_setInf A B D = D p := by
  have hK : IsCompact (A ×ˢ B) := hA.prod hB
  have hKne : (A ×ˢ B).Nonempty := hAne.prod hBne
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hKne D.continuous.continuousOn
  refine ⟨p, hp, le_antisymm (nd_pairInf_le hK D hp) ?_⟩
  exact le_csInf (hKne.image _) (by rintro _ ⟨q, hq, rfl⟩; exact hmin hq)

theorem nd_setInf_pos_of_disjoint_zeroSet {r : ℝ} (hr : 0 ≤ r) (hd : 0 < d)
    {s : nd_Joint d rGrid} (hs : s ∈ nd_pseudoSet rGrid)
    {A : Set (Rd d)} (hA : IsCompact A) (hAne : A.Nonempty)
    (hdisj : Disjoint A (nd_zeroSet r s)) :
    0 < nd_setInf A (lsph (0 : Rd d) r) s.1 := by
  obtain ⟨p, hp, hpmin⟩ := nd_exists_setInf_eq hA
    (tn_isCompact_lsph 0 r) hAne (lsph_nonempty hd 0 hr) s.1
  rw [hpmin]
  have hnonneg : 0 ≤ s.1 p := hs.2.1 p.1 p.2
  rcases lt_or_eq_of_le hnonneg with hpos | hzero
  · exact hpos
  · have hpzero : p.1 ∈ nd_zeroSet r s :=
      (nd_zeroSet_mem_iff hr hd hs p.1).2 ⟨p.2, hp.2, hzero.symm⟩
    exact False.elim ((Set.disjoint_left.mp hdisj) hp.1 hpzero)

end HigherDimLQGMetric.DGZ
