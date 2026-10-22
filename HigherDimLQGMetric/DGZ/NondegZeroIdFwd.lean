import HigherDimLQGMetric.DGZ.NondegLocalShell

/-! From a global zero-set code to the same local zero-set code. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox)

variable {d : ℕ} {rGrid : ℝ}

theorem nd_globalPointInf_le_localPointInf {r : ℝ}
    (hd : 0 < d) (hr : 0 ≤ r)
    (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i)
    (s : nd_Joint d rGrid) (hLE : s ∈ nd_globalLE rGrid i)
    (x : nd_domain rGrid i) :
    nd_pointSetInf (lsph (0 : Rd d) r) s.1 x.1 ≤
      nd_localPointInf i (nd_shellInDomain r i) (s.2 (i, 0)) x := by
  obtain ⟨y, hy, hmin⟩ := nd_exists_localPointInf_eq i
    (nd_isCompact_shellInDomain r i hsub)
    (nd_shellInDomain_nonempty hd hr i hsub)
    (s.2 (i, 0)) x
  calc
    nd_pointSetInf (lsph 0 r) s.1 x.1 ≤ s.1 (x.1, y.1) :=
      nd_pointSetInf_le (tn_isCompact_lsph 0 r) s.1 x.1 hy
    _ ≤ s.2 (i, 0) (x, y) := hLE (x, y)
    _ = nd_localPointInf i (nd_shellInDomain r i) (s.2 (i, 0)) x := hmin.symm

theorem nd_globalZero_iff_localZero_of_barrier {r : ℝ}
    (hd : 0 < d) (hr : 0 ≤ r)
    (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid)
    (hLE : s ∈ nd_globalLE rGrid i)
    (hNN : s ∈ nd_nonnegLocalSet rGrid i 0)
    (hInside : s ∈ nd_allInsideExitSet rGrid i (nd_shellInDomain r i))
    (hBarrier : 0 < nd_setInf (frontier (nd_domain rGrid i))
      (lsph (0 : Rd d) r) s.1)
    (x : nd_domain rGrid i) :
    x.1 ∈ nd_zeroSet r s ↔
      x ∈ nd_localZeroSet i (nd_shellInDomain r i) 0 s := by
  have hAimage := nd_shellInDomain_image r i hsub
  have hlocal0 : 0 ≤ nd_localPointInf i (nd_shellInDomain r i)
      (s.2 (i, 0)) x :=
    nd_localPointInf_nonneg i _ _ (fun y z => hNN (y, z)) x
  constructor
  · intro hx
    have hExit := Set.mem_iInter.mp hInside x
    change min
      (nd_internalSetInf {x} (nd_shellInDomain r i) (s.2 (i, 0)))
      (nd_setInf (frontier (nd_domain rGrid i))
        ((↑) '' nd_shellInDomain r i) s.1) ≤
      nd_setInf {x.1} ((↑) '' nd_shellInDomain r i) s.1 at hExit
    rw [hAimage, ← nd_localPointInf_eq_internalSetInf,
      ← nd_pointSetInf_eq_setInf] at hExit
    change nd_pointSetInf (lsph 0 r) s.1 x.1 = 0 at hx
    rw [hx, min_le_iff] at hExit
    change nd_localPointInf i (nd_shellInDomain r i) (s.2 (i, 0)) x = 0
    rcases hExit with hle | hle
    · exact le_antisymm hle hlocal0
    · exact False.elim ((not_le_of_gt hBarrier) hle)
  · intro hx
    change nd_localPointInf i (nd_shellInDomain r i) (s.2 (i, 0)) x = 0 at hx
    have hle := nd_globalPointInf_le_localPointInf hd hr i hsub s hLE x
    rw [hx] at hle
    exact le_antisymm hle (nd_pointSetInf_nonneg hs.2.1 x.1)

theorem nd_mem_localSelectedEq_of_globalSelectedEq {rGrid r : ℝ}
    (hd : 0 < d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (i : nd_DomainIndex d rGrid)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid)
    (hLE : s ∈ nd_globalLE rGrid i)
    (hNN : s ∈ nd_nonnegLocalSet rGrid i 0)
    (hInside : s ∈ nd_allInsideExitSet rGrid i (nd_shellInDomain r i))
    (hsel : s ∈ nd_selectedEq rGrid r i.1.1 i.1.2) :
    s ∈ nd_localSelectedEq i (nd_shellInDomain r i) 0 i.1.1 i.1.2 := by
  have hTEq : nd_thickening rGrid r i.1.1 s = nd_domain rGrid i :=
    nd_thickening_eq_domain_of_selectedEq rGrid r i s hsel
  have hEU : nd_zeroSet r s ⊆ nd_domain rGrid i := by
    rw [← hTEq]
    exact nd_zeroSet_subset_thickening hrGrid r i.1.1 s
  have hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i :=
    (nd_sphere_subset_zeroSet r hs).trans hEU
  have hfrontDisj : Disjoint (frontier (nd_domain rGrid i)) (nd_zeroSet r s) :=
    (disjoint_frontier_iff_isOpen.mpr (nd_isOpen_domain rGrid i)).mono_right hEU
  have hUne : (nd_domain rGrid i).Nonempty := by
    obtain ⟨x, hx⟩ := lsph_nonempty hd 0 hr.le
    exact ⟨x, hsub hx⟩
  have hBarrier : 0 < nd_setInf (frontier (nd_domain rGrid i))
      (lsph (0 : Rd d) r) s.1 :=
    nd_setInf_pos_of_disjoint_zeroSet hr.le hd hs
      (nd_isCompact_frontier_domain rGrid i)
      (nd_frontier_domain_nonempty hd rGrid i hUne) hfrontDisj
  intro z
  have hzEq : nd_localSelectedCell i (nd_shellInDomain r i) 0 i.1.1 s z ↔
      nd_selectedCell rGrid r i.1.1 s z := by
    constructor
    · rintro ⟨x, hx0, hxB⟩
      exact ⟨x.1, (nd_globalZero_iff_localZero_of_barrier hd hr.le i hsub s
        hs hLE hNN hInside hBarrier x).2 hx0, hxB⟩
    · rintro ⟨x, hx0, hxB⟩
      let xU : nd_domain rGrid i := ⟨x, hEU hx0⟩
      exact ⟨xU, (nd_globalZero_iff_localZero_of_barrier hd hr.le i hsub s
        hs hLE hNN hInside hBarrier xU).1 hx0, hxB⟩
  exact hzEq.trans (hsel z)

end HigherDimLQGMetric.DGZ
