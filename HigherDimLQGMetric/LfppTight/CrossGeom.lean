import HigherDimLQGMetric.LfppTight.ScaleCenter
import HigherDimLQGMetric.Sharp.ShellScaling

/-! Similarity transport for crossing observables. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_image_ball_affine {d : ℕ} {r : ℝ} (hr : 0 < r)
    (z : Rd d) (t : ℝ) :
    (fun x : Rd d => r • x + z) '' ball 0 t = ball z (r * t) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hxt : ‖x‖ < t := by simpa only [mem_ball, dist_zero_right] using hx
    exact mul_lt_mul_of_pos_left hxt hr
  · intro hy
    refine ⟨r⁻¹ • (y - z), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hr]
      have hy' : ‖y - z‖ < r * t := by simpa only [mem_ball, dist_eq_norm] using hy
      rw [inv_mul_eq_div]
      exact (div_lt_iff₀ hr).2 (by simpa only [mul_comm] using hy')
    · simp [smul_smul, hr.ne']

theorem l6a_supPairs_affine {d : ℕ} (D : Rd d × Rd d → ℝ)
    (f : Rd d → Rd d) (A : Set (Rd d)) :
    supPairs (fun p => D (f p.1, f p.2)) A = supPairs D (f '' A) := by
  unfold supPairs
  simp only [iSup_image]

theorem l6a_infPairs_affine {d : ℕ} (D : Rd d × Rd d → ℝ)
    (f : Rd d → Rd d) (A B : Set (Rd d)) :
    infPairs (fun p => D (f p.1, f p.2)) A B =
      infPairs D (f '' A) (f '' B) := by
  unfold infPairs
  simp only [iInf_image]

theorem l6a_supPairs_mul {d : ℕ} (D : Rd d × Rd d → ℝ)
    (A : Set (Rd d)) {a : ℝ} (ha : 0 ≤ a) :
    supPairs (fun p => a * D p) A = ENNReal.ofReal a * supPairs D A := by
  unfold supPairs
  simp only [ENNReal.ofReal_mul ha, ENNReal.mul_iSup]

theorem l6a_infPairs_mul {d : ℕ} (D : Rd d × Rd d → ℝ)
    (A B : Set (Rd d)) {a : ℝ} (ha : 0 < a) :
    infPairs (fun p => a * D p) A B = ENNReal.ofReal a * infPairs D A B := by
  unfold infPairs
  simp only [ENNReal.ofReal_mul ha.le,
    ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr ha).ne'
      ENNReal.ofReal_ne_top]

theorem l6a_cross_affine_of_field_eq {d : ℕ}
    (D E : Rd d × Rd d → ℝ) (f : Rd d → Rd d)
    (A B C : Set (Rd d)) {a c : ℝ} (ha : 0 < a)
    (hD : ∀ u v, D (f u, f v) = a * E (u, v))
    (hcross : supPairs E A ≤ ENNReal.ofReal c * infPairs E B C) :
    supPairs D (f '' A) ≤ ENNReal.ofReal c *
      infPairs D (f '' B) (f '' C) := by
  rw [← l6a_supPairs_affine, ← l6a_infPairs_affine]
  have heq : (fun p : Rd d × Rd d => D (f p.1, f p.2)) =
      fun p => a * E p := by
    funext p
    exact hD p.1 p.2
  rw [heq, l6a_supPairs_mul E A ha.le, l6a_infPairs_mul E B C ha]
  calc
    ENNReal.ofReal a * supPairs E A ≤
        ENNReal.ofReal a * (ENNReal.ofReal c * infPairs E B C) := by gcongr
    _ = ENNReal.ofReal c * (ENNReal.ofReal a * infPairs E B C) := by
      ac_rfl

/-- A positive scalar normalization does not change a crossing event. -/
theorem l6a_cross_iff_mul {d : ℕ} (D : Rd d × Rd d → ℝ)
    (A B C : Set (Rd d)) {a c : ℝ} (ha : 0 < a) :
    (supPairs (fun p => a * D p) A ≤
      ENNReal.ofReal c * infPairs (fun p => a * D p) B C) ↔
    (supPairs D A ≤ ENNReal.ofReal c * infPairs D B C) := by
  rw [l6a_supPairs_mul D A ha.le, l6a_infPairs_mul D B C ha]
  rw [mul_left_comm (ENNReal.ofReal c) (ENNReal.ofReal a)]
  exact ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top

end HigherDimLQGMetric
