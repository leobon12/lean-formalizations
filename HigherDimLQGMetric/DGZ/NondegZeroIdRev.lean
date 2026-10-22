import HigherDimLQGMetric.DGZ.NondegCollarAE

/-! From a local zero-set cell code to the global code, using the collar barrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ} {rGrid r : ℝ}

theorem nd_mem_globalSelectedEq_of_localSelectedEq
    (hd : 0 < d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid)
    (hLE : s ∈ nd_globalLE rGrid i)
    (hNN : s ∈ nd_nonnegLocalSet rGrid i 0)
    (hDiag : s ∈ nd_localDiagSet rGrid i 0)
    (hInside : s ∈ nd_allInsideExitSet rGrid i (nd_shellInDomain r i))
    (hOutside : s ∈ nd_allOutsideExitSet rGrid i (nd_shellInDomain r i))
    {c : ℝ} (hc : 0 < c) (hcρ : c < nd_gridRadius rGrid i.1.1)
    (hCollar : s ∈ nd_collarSet rGrid i (nd_interiorDist i) c
      (frontier (nd_domain rGrid i)) (nd_shellInDomain r i))
    (hsel : s ∈ nd_localSelectedEq i (nd_shellInDomain r i) 0 i.1.1 i.1.2) :
    s ∈ nd_selectedEq rGrid r i.1.1 i.1.2 := by
  have hlocalPos := nd_localCollarPos_of_selected hd hrGrid hr i hc hcρ
    hsub s hNN hDiag hsel
  have hBarrier : 0 < nd_setInf (frontier (nd_domain rGrid i))
      (lsph (0 : Rd d) r) s.1 := by
    have hCollar' := hCollar
    change nd_internalSetInf
      (nd_levelCollar rGrid i (nd_interiorDist i) c)
      (nd_shellInDomain r i) (s.2 (i, 0)) ≤
      nd_setInf (frontier (nd_domain rGrid i))
        ((↑) '' nd_shellInDomain r i) s.1 at hCollar'
    rw [nd_shellInDomain_image r i hsub] at hCollar'
    exact hlocalPos.trans_le hCollar'
  have hEU : nd_zeroSet r s ⊆ nd_domain rGrid i := by
    intro x hxE
    by_contra hxU
    have hExit := Set.mem_iInter.mp hOutside ⟨x, hxU⟩
    change nd_setInf (frontier (nd_domain rGrid i))
      ((↑) '' nd_shellInDomain r i) s.1 ≤
      nd_setInf {x} ((↑) '' nd_shellInDomain r i) s.1 at hExit
    rw [nd_shellInDomain_image r i hsub,
      ← nd_pointSetInf_eq_setInf] at hExit
    change nd_pointSetInf (lsph 0 r) s.1 x = 0 at hxE
    rw [hxE] at hExit
    exact (not_lt_of_ge hExit) hBarrier
  intro z
  have hzEq : nd_selectedCell rGrid r i.1.1 s z ↔
      nd_localSelectedCell i (nd_shellInDomain r i) 0 i.1.1 s z := by
    constructor
    · rintro ⟨x, hx0, hxB⟩
      let xU : nd_domain rGrid i := ⟨x, hEU hx0⟩
      exact ⟨xU, (nd_globalZero_iff_localZero_of_barrier hd hr.le i hsub s
        hs hLE hNN hInside hBarrier xU).1 hx0, hxB⟩
    · rintro ⟨x, hx0, hxB⟩
      exact ⟨x.1, (nd_globalZero_iff_localZero_of_barrier hd hr.le i hsub s
        hs hLE hNN hInside hBarrier x).2 hx0, hxB⟩
  exact hzEq.trans (hsel z)

end HigherDimLQGMetric.DGZ
