import HigherDimLQGMetric.DGZ.NondegCellMeas

/-! A bounded zero set selects only finitely many lattice cells. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox)

variable {d : ℕ}

theorem nd_selectedCell_finite {rGrid : ℝ} (hrGrid : 0 < rGrid)
    (r : ℝ) (j : ℕ) (s : nd_Joint d rGrid)
    (hbounded : Bornology.IsBounded (nd_zeroSet r s)) :
    {z : Zd d | nd_selectedCell rGrid r j s z}.Finite := by
  let ρ := nd_gridRadius rGrid j
  have hρ : 0 < ρ := nd_gridRadius_pos hrGrid j
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : Rd d)
  obtain ⟨N, hN⟩ := exists_nat_ge ((R + 2 * ρ) / ρ)
  apply finite_of_forall_withinInf (R' := (N : ℤ))
  intro z hz i
  obtain ⟨x, hx0, hxbox⟩ := hz
  have hxnorm : ‖x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx0
  have hxi : |x i| ≤ R := (HigherDimLFPP.DGZ.abs_apply_le_norm x i).trans hxnorm
  have hboxi : |x i - ρ * (z i : ℝ)| < 2 * ρ := by
    simpa only [latPt] using hxbox i
  have hupper : (z i : ℝ) ≤ (N : ℝ) := by
    have hzi : (z i : ℝ) ≤ (R + 2 * ρ) / ρ := by
      apply (le_div_iff₀ hρ).2
      have := (abs_le.mp hxi).2
      have := (abs_lt.mp hboxi).1
      linarith
    exact hzi.trans hN
  have hlower : -(N : ℝ) ≤ (z i : ℝ) := by
    have hzi : -(R + 2 * ρ) / ρ ≤ (z i : ℝ) := by
      apply (div_le_iff₀ hρ).2
      have := (abs_le.mp hxi).1
      have := (abs_lt.mp hboxi).2
      linarith
    rw [neg_div] at hzi
    linarith [hN]
  have habs : |(z i : ℝ)| ≤ (N : ℝ) := abs_le.mpr ⟨hlower, hupper⟩
  have habsInt : |z i| ≤ (N : ℤ) := by exact_mod_cast habs
  simpa [WithinInf] using habsInt

end HigherDimLQGMetric.DGZ
