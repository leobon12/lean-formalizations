import HigherDimLQGMetric.DGZ.NondegLocalEvent

/-! The cubical shell as a compact subset of a containing local domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ} {rGrid : ℝ}

def nd_shellInDomain (r : ℝ) (i : nd_DomainIndex d rGrid) :
    Set (nd_domain rGrid i) :=
  {x | (x : Rd d) ∈ lsph (0 : Rd d) r}

theorem nd_shellInDomain_image (r : ℝ) (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i) :
    ((↑) '' nd_shellInDomain r i : Set (Rd d)) = lsph (0 : Rd d) r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨⟨y, hsub hy⟩, hy, rfl⟩

theorem nd_isCompact_shellInDomain (r : ℝ) (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i) :
    IsCompact (nd_shellInDomain r i) := by
  rw [Subtype.isCompact_iff, nd_shellInDomain_image r i hsub]
  exact tn_isCompact_lsph 0 r

theorem nd_shellInDomain_nonempty (hd : 0 < d) {r : ℝ} (hr : 0 ≤ r)
    (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i) :
    (nd_shellInDomain r i).Nonempty := by
  obtain ⟨y, hy⟩ := lsph_nonempty hd 0 hr
  exact ⟨⟨y, hsub hy⟩, hy⟩

end HigherDimLQGMetric.DGZ
