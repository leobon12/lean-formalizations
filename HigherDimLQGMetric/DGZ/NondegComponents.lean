import HigherDimLQGMetric.DGZ.NondegShellConn

/-!
The component of a finite open box union is again a finite open box union.
Its frontier lies outside the original union. These deterministic facts permit
the exit inequality to force all zero-distance points into one component.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox)

variable {d : ℕ}

theorem nd_isConnected_cell {rGrid : ℝ} (hrGrid : 0 < rGrid)
    (j : ℕ) (z : Zd d) :
    IsConnected (obox (latPt (nd_gridRadius rGrid j) z)
      (2 * nd_gridRadius rGrid j)) :=
  (HigherDimLFPP.DGZ.convex_obox _ _).isConnected
    ⟨_, HigherDimLFPP.DGZ.mem_obox_self _
      (by have := nd_gridRadius_pos hrGrid j; linarith)⟩

theorem nd_cell_subset_component {rGrid : ℝ} (hrGrid : 0 < rGrid)
    (j : ℕ) (S : Finset (Zd d)) (z : Zd d) (hz : z ∈ S)
    (x₀ : Rd d)
    (hinter : (obox (latPt (nd_gridRadius rGrid j) z)
      (2 * nd_gridRadius rGrid j) ∩
      connectedComponentIn (nd_boxUnion rGrid j S) x₀).Nonempty) :
    obox (latPt (nd_gridRadius rGrid j) z)
      (2 * nd_gridRadius rGrid j) ⊆
      connectedComponentIn (nd_boxUnion rGrid j S) x₀ := by
  let B := obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)
  let U := nd_boxUnion rGrid j S
  obtain ⟨q, hqB, hqC⟩ := hinter
  have hBU : B ⊆ U := fun x hx => Set.mem_iUnion.2
    ⟨z, Set.mem_iUnion.2 ⟨hz, hx⟩⟩
  have hB : B ⊆ connectedComponentIn U q :=
    (nd_isConnected_cell hrGrid j z).isPreconnected.subset_connectedComponentIn hqB hBU
  rw [connectedComponentIn_eq hqC]
  exact hB

theorem nd_exists_component_boxUnion {rGrid : ℝ} (hrGrid : 0 < rGrid)
    (j : ℕ) (S : Finset (Zd d)) (x₀ : Rd d)
    (hx₀ : x₀ ∈ nd_boxUnion rGrid j S) :
    ∃ S₀ : Finset (Zd d), S₀ ⊆ S ∧
      nd_boxUnion rGrid j S₀ =
        connectedComponentIn (nd_boxUnion rGrid j S) x₀ ∧
      IsConnected (nd_boxUnion rGrid j S₀) ∧
      frontier (nd_boxUnion rGrid j S₀) ∩ nd_boxUnion rGrid j S = ∅ := by
  classical
  let U := nd_boxUnion rGrid j S
  let C := connectedComponentIn U x₀
  let S₀ := S.filter fun z =>
    (obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j) ∩ C).Nonempty
  have hsub : S₀ ⊆ S := Finset.filter_subset _ _
  have hCeq : nd_boxUnion rGrid j S₀ = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, hxB⟩ := (by simpa only [nd_boxUnion, Set.mem_iUnion] using hx :
        ∃ z : Zd d, ∃ (_ : z ∈ S₀),
          x ∈ obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j))
      exact nd_cell_subset_component hrGrid j S z (hsub hz) x₀
        (Finset.mem_filter.mp hz).2 hxB
    · intro hx
      have hxU : x ∈ U := connectedComponentIn_subset U x₀ hx
      obtain ⟨z, hz, hxB⟩ := (by simpa only [U, nd_boxUnion, Set.mem_iUnion] using hxU :
        ∃ z : Zd d, ∃ (_ : z ∈ S),
          x ∈ obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j))
      have hz₀ : z ∈ S₀ := Finset.mem_filter.mpr ⟨hz, ⟨x, hxB, hx⟩⟩
      exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hz₀, hxB⟩⟩
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hx₀
  have hCfront : frontier C ∩ U = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hpCl : p ∈ closure C := hp.1.1
    have hpU : p ∈ U := hp.2
    have hCopen : IsOpen C := (nd_isOpen_boxUnion rGrid j S).connectedComponentIn
    have hpNotC : p ∉ C := by
      rw [← hCopen.interior_eq]
      exact hp.1.2
    obtain ⟨z, hz, hpB⟩ := (by simpa only [U, nd_boxUnion, Set.mem_iUnion] using hpU :
      ∃ z : Zd d, ∃ (_ : z ∈ S),
        p ∈ obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j))
    have hBopen : IsOpen
        (obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)) :=
      HigherDimLFPP.DGZ.isOpen_obox _ _
    obtain ⟨q, hqB, hqC⟩ :=
      (mem_closure_iff_nhds.mp hpCl _ (hBopen.mem_nhds hpB))
    exact hpNotC (nd_cell_subset_component hrGrid j S z hz x₀
      ⟨q, hqB, hqC⟩ hpB)
  exact ⟨S₀, hsub, hCeq, hCeq ▸ hCconn, hCeq ▸ hCfront⟩

end HigherDimLQGMetric.DGZ
