import HigherDimLQGMetric.Shell.Defs
import HigherDimLFPP.Var.Coord

/-! A nearest grid point in `sℤ^d`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem exists_gridPt_near {s : ℝ} (hs : 0 < s) (x : Rd d) :
    ∃ w ∈ gridPts s, ‖x - w‖ ≤ (d : ℝ) * s := by
  let m : Fin d → ℤ := fun i => ⌊x i / s⌋
  let w : Rd d := WithLp.toLp 2 (fun i => s * (m i : ℝ))
  refine ⟨w, ⟨m, rfl⟩, ?_⟩
  have hcoord (i : Fin d) : |(x - w) i| ≤ s := by
    have hnonneg : 0 ≤ x i - (m i : ℝ) * s := by
      have hfl := Int.floor_le (x i / s)
      have hmul := mul_le_mul_of_nonneg_right hfl hs.le
      rw [div_mul_cancel₀ _ hs.ne'] at hmul
      exact sub_nonneg.2 hmul
    have hlt : x i - (m i : ℝ) * s < s := Int.sub_floor_div_mul_lt (x i) hs
    change |x i - s * (m i : ℝ)| ≤ s
    rw [mul_comm s, abs_of_nonneg hnonneg]
    exact hlt.le
  calc
    ‖x - w‖ ≤ ∑ i : Fin d, |(x - w) i| := HigherDimLFPP.Var.norm_le_sum_abs _
    _ ≤ ∑ _i : Fin d, s := Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * s := by simp [mul_comm]

end HigherDimLQGMetric
