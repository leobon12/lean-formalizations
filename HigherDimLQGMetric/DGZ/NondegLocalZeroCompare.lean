import HigherDimLQGMetric.DGZ.NondegZeroIdRev

/-! Finite local comparison constants preserve zero distance to the reference shell. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ} {rGrid r : ℝ}

theorem nd_localPointInf_zero_iff_of_finiteCompSet
    (hd : 0 < d) (hr : 0 ≤ r) (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i)
    (m : ℕ) (s : nd_Joint d rGrid)
    (hcomp : s ∈ nd_finiteCompSet rGrid i m)
    (hNN0 : s ∈ nd_nonnegLocalSet rGrid i 0)
    (hNNm : s ∈ nd_nonnegLocalSet rGrid i m)
    (x : nd_domain rGrid i) :
    x ∈ nd_localZeroSet i (nd_shellInDomain r i) 0 s ↔
      x ∈ nd_localZeroSet i (nd_shellInDomain r i) m s := by
  have hAcomp := nd_isCompact_shellInDomain r i hsub
  have hAne := nd_shellInDomain_nonempty hd hr i hsub
  constructor
  · intro hx
    obtain ⟨y, hy, hmin⟩ := nd_exists_localPointInf_eq i hAcomp hAne
      (s.2 (i, 0)) x
    have hpair : s.2 (i, m) (x, y) = 0 :=
      (nd_localZero_iff_of_finiteCompSet rGrid i m hcomp hNN0 hNNm (x, y)).1
        (hmin ▸ hx)
    exact le_antisymm ((nd_localPointInf_le i hAcomp _ x hy).trans_eq hpair)
      (nd_localPointInf_nonneg i _ _ (fun a b => hNNm (a, b)) x)
  · intro hx
    obtain ⟨y, hy, hmin⟩ := nd_exists_localPointInf_eq i hAcomp hAne
      (s.2 (i, m)) x
    have hpair : s.2 (i, 0) (x, y) = 0 :=
      (nd_localZero_iff_of_finiteCompSet rGrid i m hcomp hNN0 hNNm (x, y)).2
        (hmin ▸ hx)
    exact le_antisymm ((nd_localPointInf_le i hAcomp _ x hy).trans_eq hpair)
      (nd_localPointInf_nonneg i _ _ (fun a b => hNN0 (a, b)) x)

theorem nd_localSelectedEq_iff_of_finiteCompSet
    (hd : 0 < d) (hr : 0 ≤ r) (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i)
    (m j : ℕ) (S : Finset (Zd d)) (s : nd_Joint d rGrid)
    (hcomp : s ∈ nd_finiteCompSet rGrid i m)
    (hNN0 : s ∈ nd_nonnegLocalSet rGrid i 0)
    (hNNm : s ∈ nd_nonnegLocalSet rGrid i m) :
    s ∈ nd_localSelectedEq i (nd_shellInDomain r i) 0 j S ↔
      s ∈ nd_localSelectedEq i (nd_shellInDomain r i) m j S := by
  have hz (z : Zd d) : nd_localSelectedCell i (nd_shellInDomain r i) 0 j s z ↔
      nd_localSelectedCell i (nd_shellInDomain r i) m j s z := by
    constructor
    · rintro ⟨x, hx, hbox⟩
      exact ⟨x, (nd_localPointInf_zero_iff_of_finiteCompSet hd hr i hsub m s
        hcomp hNN0 hNNm x).1 hx, hbox⟩
    · rintro ⟨x, hx, hbox⟩
      exact ⟨x, (nd_localPointInf_zero_iff_of_finiteCompSet hd hr i hsub m s
        hcomp hNN0 hNNm x).2 hx, hbox⟩
  constructor
  · intro hs z
    exact (hz z).symm.trans (hs z)
  · intro hs z
    exact (hz z).trans (hs z)

end HigherDimLQGMetric.DGZ
