import HigherDimLQGMetric.DGZ.NondegPairBound

/-! Separated selected indices give membership in the countable pair event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_mem_sepPairEvent_of_selected
    {rGrid r : ℝ} (hrGrid : 0 < rGrid) (j : ℕ)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid)
    (i₁ i₂ : nd_DomainIndex d rGrid)
    (hj₁ : i₁.1.1 = j) (hj₂ : i₂.1.1 = j)
    (hsel₁ : s ∈ nd_selectedEq rGrid r i₁.1.1 i₁.1.2)
    (hsel₂ : s ∈ nd_selectedEq rGrid (2 * r) i₂.1.1 i₂.1.2)
    (hsep : nd_domainSeparated rGrid i₁ i₂) :
    s ∈ nd_sepPairEvent rGrid r j := by
  have hsub₁ := nd_shell_subset_domain_of_selected hrGrid i₁ s hs hsel₁
  have hsub₂ := nd_shell_subset_domain_of_selected hrGrid i₂ s hs hsel₂
  have hdisj := nd_domainSeparated_disjoint rGrid i₁ i₂ hsep
  let g₁ : nd_GoodIndex (d := d) rGrid r (2 * r) j :=
    ⟨i₁, hj₁, hsub₁, hdisj.mono_right hsub₂⟩
  let g₂ : nd_GoodIndex (d := d) rGrid (2 * r) r j :=
    ⟨i₂, hj₂, hsub₂, hdisj.symm.mono_right hsub₁⟩
  rw [nd_sepPairEvent_eq]
  apply Set.mem_iUnion.2
  refine ⟨(g₁, g₂), ?_⟩
  simpa [g₁, g₂, hsep, nd_goodCodeEvent] using
    (show s ∈ nd_selectedEq rGrid r i₁.1.1 i₁.1.2 ∩
      nd_selectedEq rGrid (2 * r) i₂.1.1 i₂.1.2 from ⟨hsel₁, hsel₂⟩)

end HigherDimLQGMetric.DGZ
