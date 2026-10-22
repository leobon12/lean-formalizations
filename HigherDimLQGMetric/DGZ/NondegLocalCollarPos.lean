import HigherDimLQGMetric.DGZ.NondegLocalBarrier

/-! A local selected-cell code puts its zero set strictly inside the domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ} {rGrid r : ℝ}

theorem nd_shellInDomain_subset_localZero
    (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i)
    (s : nd_Joint d rGrid)
    (hNN : s ∈ nd_nonnegLocalSet rGrid i 0)
    (hDiag : s ∈ nd_localDiagSet rGrid i 0) :
    nd_shellInDomain r i ⊆ nd_localZeroSet i (nd_shellInDomain r i) 0 s := by
  intro x hx
  have hA := nd_isCompact_shellInDomain r i hsub
  have hle := nd_localPointInf_le i hA (s.2 (i, 0)) x hx
  have hzero : s.2 (i, 0) (x, x) = 0 := hDiag x
  rw [hzero] at hle
  exact le_antisymm hle
    (nd_localPointInf_nonneg i _ _ (fun y z => hNN (y, z)) x)

theorem nd_localCollarPos_of_selected {rGrid r : ℝ}
    (hd : 0 < d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (i : nd_DomainIndex d rGrid)
    {c : ℝ} (hc : 0 < c) (hcρ : c < nd_gridRadius rGrid i.1.1)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i)
    (s : nd_Joint d rGrid)
    (hNN : s ∈ nd_nonnegLocalSet rGrid i 0)
    (hDiag : s ∈ nd_localDiagSet rGrid i 0)
    (hsel : s ∈ nd_localSelectedEq i (nd_shellInDomain r i) 0 i.1.1 i.1.2) :
    0 < nd_internalSetInf
      (nd_levelCollar rGrid i (nd_interiorDist i)
        c)
      (nd_shellInDomain r i) (s.2 (i, 0)) := by
  let ρ := nd_gridRadius rGrid i.1.1
  let g := nd_interiorDist i
  let K := nd_levelCollar rGrid i g c
  let A := nd_shellInDomain r i
  have hρ : 0 < ρ := nd_gridRadius_pos hrGrid i.1.1
  have hg : Continuous g := nd_continuous_interiorDist i
  have hgU : ∀ z, z ∉ nd_domain rGrid i → g z ≤ 0 := by
    intro z hz
    exact le_of_eq (nd_interiorDist_eq_zero_of_not_mem i hz)
  have hAcomp : IsCompact A := nd_isCompact_shellInDomain r i hsub
  have hAne : A.Nonempty := nd_shellInDomain_nonempty hd hr.le i hsub
  have hKcomp : IsCompact K := nd_isCompact_levelCollar rGrid i hg hc hgU
  have hShellZero := nd_shellInDomain_subset_localZero i hsub s hNN hDiag
  have hKne : K.Nonempty := by
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨b, hb⟩ := nd_frontier_domain_nonempty hd rGrid i
      (nd_isConnected_domain rGrid i).nonempty
    have ha0 : a ∈ nd_localZeroSet i A 0 s := hShellZero ha
    have hga : ρ ≤ g (a : Rd d) :=
      nd_infDist_compl_ge_grid_of_localZero hd hrGrid i A 0 s hsel a ha0
    have hgb : g b ≤ 0 := le_of_eq (nd_interiorDist_frontier_zero i hb)
    exact nd_levelCollar_nonempty_of_inside hg hgU hc hcρ.le a hga b hgb
  have hKdisj : Disjoint K (nd_localZeroSet i A 0 s) := by
    rw [Set.disjoint_left]
    intro x hxK hx0
    have hxg : g (x : Rd d) = c := hxK
    have hge : ρ ≤ g (x : Rd d) :=
      nd_infDist_compl_ge_grid_of_localZero hd hrGrid i A 0 s hsel x hx0
    linarith
  exact nd_internalSetInf_pos_of_disjoint_localZero i hKcomp hAcomp
    hKne hAne (s.2 (i, 0)) (fun x y => hNN (x, y)) hKdisj

end HigherDimLQGMetric.DGZ
