import HigherDimLQGMetric.Events.Defs
import HigherDimLFPP.Field.OscBlock
import HigherDimLFPP.Exist.Discretize

/-!
# Finite grids for rounded-centre shell covering
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt roundLat)

variable {d : ℕ}

/-- Coordinatewise lattice rounding has Euclidean error bounded by `√d` times the mesh. -/
theorem shellCover_roundLat_dist_le {s : ℝ} (hs : 0 < s) (x : Rd d) :
    ‖x - latPt s (roundLat s x)‖ ≤ √(d : ℝ) * s := by
  apply (HigherDimLFPP.Osc.norm_sub_le_sqrt_mul _ _).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hs.le).2
  intro i
  have hi := HigherDimLFPP.DGZ.abs_latPt_roundLat_sub_lt hs x i
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] using hi.le

theorem shellCover_sqrt_dim_le (hd : 1 ≤ d) : √(d : ℝ) ≤ d := by
  have h : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : (√(d : ℝ)) ^ 2 = d := Real.sq_sqrt (by positivity)
  nlinarith [Real.sqrt_nonneg (d : ℝ)]

/-- A dimension-free convenient weakening of the rounding estimate. -/
theorem shellCover_roundLat_dist_le_dim (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s)
    (x : Rd d) : ‖x - latPt s (roundLat s x)‖ ≤ (d : ℝ) * s :=
  (shellCover_roundLat_dist_le hs x).trans
    (mul_le_mul_of_nonneg_right (shellCover_sqrt_dim_le hd) hs.le)

/-- A convenient weakening of the finite box-grid approximation estimate. -/
theorem shellCover_gridOf_dist_le_dim (hd : 1 ≤ d) (B : ℝ) {η : ℝ} (hη : 0 < η)
    {x : Rd d} (hx : x ∈ HigherDimLFPP.Osc.box 0 B) :
    ‖x - HigherDimLFPP.Osc.gridOf 0 B η x‖ ≤ (d : ℝ) * η :=
  (HigherDimLFPP.Osc.norm_sub_gridOf_le 0 hη hx).trans
    (mul_le_mul_of_nonneg_right (shellCover_sqrt_dim_le hd) hη.le)

end HigherDimLQGMetric
