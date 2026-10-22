import HigherDimLQGMetric.DGZ.NondegLocalCollarPos

/-! Choose a deterministic collar level below both the grid mesh and the shell's clearance. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ} {rGrid r : ℝ}

theorem nd_exists_shellCollarLevel (hd : 0 < d)
    (hrGrid : 0 < rGrid) (hr : 0 < r)
    (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i) :
    ∃ c : ℝ, 0 < c ∧ c < nd_gridRadius rGrid i.1.1 ∧
      ∀ x ∈ nd_shellInDomain r i, c ≤ nd_interiorDist i x.1 := by
  let A := nd_shellInDomain r i
  let g := nd_interiorDist i
  let ρ := nd_gridRadius rGrid i.1.1
  have hAcomp : IsCompact A := nd_isCompact_shellInDomain r i hsub
  have hAne : A.Nonempty := nd_shellInDomain_nonempty hd hr.le i hsub
  have hg : Continuous fun x : nd_domain rGrid i => g x.1 :=
    (nd_continuous_interiorDist i).comp continuous_subtype_val
  obtain ⟨x₀, hx₀, hmin⟩ := hAcomp.exists_isMinOn hAne hg.continuousOn
  have hUcompne : (nd_domain rGrid i)ᶜ.Nonempty := nd_domain_compl_nonempty hd i
  have hpos : 0 < g x₀.1 :=
    ((nd_isOpen_domain rGrid i).isClosed_compl.notMem_iff_infDist_pos hUcompne).mp
      (show x₀.1 ∉ (nd_domain rGrid i)ᶜ from fun hx => hx x₀.2)
  have hρ : 0 < ρ := nd_gridRadius_pos hrGrid i.1.1
  refine ⟨min (g x₀.1) (ρ / 2), lt_min hpos (half_pos hρ), ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (half_lt_self hρ)
  · intro x hx
    exact (min_le_left _ _).trans (hmin hx)

end HigherDimLQGMetric.DGZ
