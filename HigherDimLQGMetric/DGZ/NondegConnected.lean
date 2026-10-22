import HigherDimLQGMetric.DGZ.NondegBarrier

/-!
The exit inequality forces a finite thickening of the zero set to be connected.
Every selected wide cell actually meets the zero set, so once the zero set is
inside the component containing the shell, all selected cells are there too.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox)

variable {d : ℕ}

theorem nd_isConnected_thickening_of_exit {rGrid r : ℝ}
    (hd : 2 ≤ d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (j : ℕ) (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid)
    (S : Finset (Zd d)) (hsel : s ∈ nd_selectedEq rGrid r j S)
    (hExit : ∀ i : nd_DomainIndex d rGrid,
      lsph (0 : Rd d) r ⊆ nd_domain rGrid i →
      ∀ x : Rd d, x ∉ nd_domain rGrid i →
        nd_setInf (frontier (nd_domain rGrid i)) (lsph 0 r) s.1 ≤
          nd_pointSetInf (lsph 0 r) s.1 x) :
    IsConnected (nd_thickening rGrid r j s) := by
  let T := nd_thickening rGrid r j s
  have hTEq : T = nd_boxUnion rGrid j S :=
    nd_thickening_eq_boxUnion_of_selected rGrid r j s S hsel
  have hSphereE : lsph (0 : Rd d) r ⊆ nd_zeroSet r s :=
    nd_sphere_subset_zeroSet r hs
  have hET : nd_zeroSet r s ⊆ T := nd_zeroSet_subset_thickening hrGrid r j s
  have hSphereT : lsph (0 : Rd d) r ⊆ nd_boxUnion rGrid j S := by
    rw [← hTEq]
    exact hSphereE.trans hET
  obtain ⟨x₀, hx₀Sphere⟩ := lsph_nonempty (by omega : 0 < d) 0 hr.le
  have hx₀T : x₀ ∈ nd_boxUnion rGrid j S := hSphereT hx₀Sphere
  obtain ⟨S₀, hS₀S, hCeq, hCconn, hCfront⟩ :=
    nd_exists_component_boxUnion hrGrid j S x₀ hx₀T
  let i₀ : nd_DomainIndex d rGrid := ⟨(j, S₀), hCconn⟩
  have hUeq : nd_domain rGrid i₀ =
      connectedComponentIn (nd_boxUnion rGrid j S) x₀ := hCeq
  have hSphereU : lsph (0 : Rd d) r ⊆ nd_domain rGrid i₀ := by
    rw [hUeq]
    exact (nd_isConnected_lsph hd hr.le).isPreconnected.subset_connectedComponentIn
      hx₀Sphere hSphereT
  have hEU : nd_zeroSet r s ⊆ nd_domain rGrid i₀ := by
    have hfrontDisj : Disjoint (frontier (nd_domain rGrid i₀)) (nd_zeroSet r s) := by
      rw [Set.disjoint_left]
      intro x hxFront hxE
      have hxT : x ∈ nd_boxUnion rGrid j S := hTEq ▸ hET hxE
      exact (Set.eq_empty_iff_forall_notMem.mp hCfront x) ⟨hxFront, hxT⟩
    have hUne : (nd_domain rGrid i₀).Nonempty := ⟨x₀, hSphereU hx₀Sphere⟩
    have hbarrier : 0 < nd_setInf (frontier (nd_domain rGrid i₀))
        (lsph (0 : Rd d) r) s.1 :=
      nd_setInf_pos_of_disjoint_zeroSet hr.le (by omega : 0 < d) hs
        (nd_isCompact_frontier_domain rGrid i₀)
        (nd_frontier_domain_nonempty (by omega : 0 < d) rGrid i₀ hUne)
        hfrontDisj
    intro x hxE
    by_contra hxU
    have hle := hExit i₀ hSphereU x hxU
    change nd_pointSetInf (lsph 0 r) s.1 x = 0 at hxE
    rw [hxE] at hle
    exact (not_lt_of_ge hle) hbarrier
  have hTS : T ⊆ nd_domain rGrid i₀ := by
    intro x hxT
    rw [hTEq] at hxT
    obtain ⟨z, hzS, hxB⟩ := (by simpa only [nd_boxUnion, Set.mem_iUnion] using hxT :
      ∃ z : Zd d, ∃ (_ : z ∈ S),
        x ∈ obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j))
    have hzSel : nd_selectedCell rGrid r j s z := (hsel z).2 hzS
    obtain ⟨y, hyE, hyB⟩ := hzSel
    have hBC : obox (latPt (nd_gridRadius rGrid j) z)
        (2 * nd_gridRadius rGrid j) ⊆
        connectedComponentIn (nd_boxUnion rGrid j S) x₀ :=
      nd_cell_subset_component hrGrid j S z hzS x₀
        ⟨y, hyB, hUeq ▸ hEU hyE⟩
    exact hUeq ▸ hBC hxB
  have hUT : nd_domain rGrid i₀ ⊆ T := by
    rw [hTEq]
    intro x hx
    obtain ⟨z, hz, hxB⟩ := (by simpa only [nd_domain, nd_boxUnion, Set.mem_iUnion] using hx :
      ∃ z : Zd d, ∃ (_ : z ∈ S₀),
        x ∈ obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j))
    exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hS₀S hz, hxB⟩⟩
  have hEq : T = nd_domain rGrid i₀ := Set.Subset.antisymm hTS hUT
  change IsConnected T
  rw [hEq]
  exact nd_isConnected_domain rGrid i₀

end HigherDimLQGMetric.DGZ
