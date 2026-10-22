import HigherDimLQGContinuity.Caps.Lemma22
import HigherDimLQGContinuity.Caps.FullScales

/-!
# Full-window sites belong to the cap's inspected grid
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

theorem q11_primary_grid_mem {d : ℕ} {V : ℝ} (hV : 0 ≤ V)
    {n : ℕ} (hn : 2 * V ≤ (n : ℝ))
    {k : ℕ} (hk : k ∈ p4_fullScales V)
    {j : Fin d → ℤ} {z : Rd d}
    (hz : z = latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j)
    (hz4 : ‖z‖ ≤ 4) :
    (p4_radius k, z) ∈
      gridPairs d 2 (1 / (20 * Real.sqrt d)) n 4 := by
  have hrad : Real.exp (-2 * V) ≤ p4_radius k :=
    ((p4_mem_fullScales_iff hV k).mp hk).1
  have hlow : Real.exp (-(n : ℝ)) ≤ p4_radius k :=
    (Real.exp_le_exp.mpr (by linarith)).trans hrad
  change ∃ l : ℕ, p4_radius k = (2 : ℝ) ^ (-(l : ℝ)) ∧
    Real.exp (-(n : ℝ)) ≤ p4_radius k ∧
      ∃ i : Fin d → ℤ,
        z = latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) i ∧ ‖z‖ ≤ 4
  exact ⟨k, rfl, hlow, j, hz, hz4⟩

end HigherDimLQGContinuity
