import HigherDimLQGMetric.DGZ.NondegSelectedIndep
import HigherDimLFPP.Upper.LocalMeanShells

/-! Every point of a selected cubical thickening lies close to its zero set. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox)

variable {d : ℕ}

theorem nd_near_zero_of_mem_thickening {rGrid r : ℝ} (hrGrid : 0 < rGrid)
    (j : ℕ) (s : nd_Joint d rGrid) {y : Rd d}
    (hy : y ∈ nd_thickening rGrid r j s) :
    ∃ x ∈ nd_zeroSet r s,
      ‖y - x‖ ≤ Real.sqrt d * (4 * nd_gridRadius rGrid j) := by
  simp only [nd_thickening, Set.mem_iUnion] at hy
  obtain ⟨z, ⟨x, hx, hxbox⟩, hybox⟩ := hy
  let ρ := nd_gridRadius rGrid j
  have hρ : 0 < ρ := nd_gridRadius_pos hrGrid j
  have hpi : ‖WithLp.ofLp (y - x)‖ ≤ 4 * ρ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro k
    simp only [WithLp.ofLp_sub, Pi.sub_apply, Real.norm_eq_abs]
    have h₁ := hybox k
    have h₂ := hxbox k
    have htri : |y k - x k| ≤ |y k - latPt ρ z k| +
        |latPt ρ z k - x k| := by
      calc
        |y k - x k| = |(y k - latPt ρ z k) +
            (latPt ρ z k - x k)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    rw [abs_sub_comm] at h₂
    linarith
  refine ⟨x, hx, ?_⟩
  exact (HigherDimLFPP.Upper.norm_le_sqrt_mul_sup (y - x)).trans
    (mul_le_mul_of_nonneg_left hpi (Real.sqrt_nonneg _))

theorem nd_near_zero_of_mem_domain {rGrid r : ℝ} (hrGrid : 0 < rGrid)
    (i : nd_DomainIndex d rGrid) (s : nd_Joint d rGrid)
    (hsel : s ∈ nd_selectedEq rGrid r i.1.1 i.1.2)
    {y : Rd d} (hy : y ∈ nd_domain rGrid i) :
    ∃ x ∈ nd_zeroSet r s,
      ‖y - x‖ ≤ Real.sqrt d * (4 * nd_gridRadius rGrid i.1.1) := by
  apply nd_near_zero_of_mem_thickening hrGrid i.1.1 s
  rw [nd_thickening_eq_domain_of_selectedEq rGrid r i s hsel]
  exact hy

end HigherDimLQGMetric.DGZ
