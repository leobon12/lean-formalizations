import HigherDimLQGMetric.DGZ.NondegZeroIdFwd

/-!
If the local zero-set cell code is a finite domain, every local zero has a full
Euclidean ball of one grid mesh inside that domain. This supplies the collar
separation used in the reverse event identification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox roundLat abs_latPt_roundLat_sub_lt)

variable {d : ℕ} {rGrid : ℝ}

theorem nd_domain_compl_nonempty (hd : 0 < d)
    (i : nd_DomainIndex d rGrid) :
    (nd_domain rGrid i)ᶜ.Nonempty := by
  obtain ⟨y, hy⟩ := nd_frontier_domain_nonempty hd rGrid i
    (nd_isConnected_domain rGrid i).nonempty
  have hdisj : Disjoint (frontier (nd_domain rGrid i)) (nd_domain rGrid i) :=
    disjoint_frontier_iff_isOpen.mpr (nd_isOpen_domain rGrid i)
  exact ⟨y, (Set.disjoint_left.mp hdisj) hy⟩

theorem nd_ball_subset_domain_of_localZero {rGrid : ℝ} (hrGrid : 0 < rGrid)
    (i : nd_DomainIndex d rGrid) (A : Set (nd_domain rGrid i)) (m : ℕ)
    (s : nd_Joint d rGrid)
    (hsel : s ∈ nd_localSelectedEq i A m i.1.1 i.1.2)
    (x : nd_domain rGrid i) (hx0 : x ∈ nd_localZeroSet i A m s) :
    Metric.ball (x : Rd d) (nd_gridRadius rGrid i.1.1) ⊆ nd_domain rGrid i := by
  let ρ := nd_gridRadius rGrid i.1.1
  have hρ : 0 < ρ := nd_gridRadius_pos hrGrid i.1.1
  let z := roundLat ρ (x : Rd d)
  have hxB : (x : Rd d) ∈ obox (latPt ρ z) (2 * ρ) := by
    intro k
    have hk := abs_latPt_roundLat_sub_lt hρ (x : Rd d) k
    rw [abs_sub_comm] at hk
    linarith
  have hzSel : nd_localSelectedCell i A m i.1.1 s z := ⟨x, hx0, hxB⟩
  have hzS : z ∈ i.1.2 := (hsel z).mp hzSel
  intro y hy
  have hyB : y ∈ obox (latPt ρ z) (2 * ρ) := by
    intro k
    have hxy : |y k - x.1 k| < ρ := by
      have hcoord := HigherDimLFPP.DGZ.abs_apply_le_norm (y - x.1) k
      have hdist : ‖y - x.1‖ < ρ := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
      have heq : (y - x.1) k = y k - x.1 k := rfl
      rw [heq] at hcoord
      exact hcoord.trans_lt hdist
    have hxz := abs_latPt_roundLat_sub_lt hρ (x : Rd d) k
    have htri : |y k - latPt ρ z k| ≤ |y k - x.1 k| + |x.1 k - latPt ρ z k| := by
      calc
        |y k - latPt ρ z k| = |(y k - x.1 k) + (x.1 k - latPt ρ z k)| := by
          congr 1
          ring
        _ ≤ _ := abs_add_le _ _
    rw [abs_sub_comm] at hxz
    linarith
  change y ∈ nd_boxUnion rGrid i.1.1 i.1.2
  exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzS, hyB⟩⟩

theorem nd_infDist_compl_ge_grid_of_localZero (hd : 0 < d)
    {rGrid : ℝ} (hrGrid : 0 < rGrid)
    (i : nd_DomainIndex d rGrid) (A : Set (nd_domain rGrid i)) (m : ℕ)
    (s : nd_Joint d rGrid)
    (hsel : s ∈ nd_localSelectedEq i A m i.1.1 i.1.2)
    (x : nd_domain rGrid i) (hx0 : x ∈ nd_localZeroSet i A m s) :
    nd_gridRadius rGrid i.1.1 ≤ Metric.infDist (x : Rd d) (nd_domain rGrid i)ᶜ := by
  have hball := nd_ball_subset_domain_of_localZero hrGrid i A m s hsel x hx0
  apply (Metric.le_infDist (nd_domain_compl_nonempty hd i)).2
  intro y hy
  by_contra hnot
  have hdist : dist (x : Rd d) y < nd_gridRadius rGrid i.1.1 := lt_of_not_ge hnot
  exact hy (hball (by simpa only [Metric.mem_ball, dist_comm] using hdist))

end HigherDimLQGMetric.DGZ
