import HigherDimLQGMetric.Sharp.ScaledMetric
import HigherDimLQGMetric.Shell.Defs

/-! Coordinate and scalar changes of shell observables. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem norm_affine_sub (r : ℝ) (z x : Rd d) :
    ‖r • x + z - z‖ = |r| * ‖x‖ := by
  rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs]

theorem image_sphere_affine {r : ℝ} (hr : 0 < r) (z : Rd d) (t : ℝ) :
    (fun x : Rd d => r • x + z) '' sphere 0 t = sphere z (r * t) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_sphere, dist_eq_norm, norm_affine_sub, abs_of_pos hr]
    have hxt : ‖x‖ = t := by simpa only [mem_sphere, dist_eq_norm, sub_zero] using hx
    rw [hxt]
  · intro hy
    refine ⟨r⁻¹ • (y - z), ?_, ?_⟩
    · rw [mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hr]
      have hy' : ‖y - z‖ = r * t := by simpa only [mem_sphere, dist_eq_norm] using hy
      rw [hy']
      field_simp
    · simp [smul_smul, hr.ne']

theorem image_ann_affine {r : ℝ} (hr : 0 < r) (z : Rd d) (a b : ℝ) :
    (fun x : Rd d => r • x + z) '' ann 0 a b = ann z (r * a) (r * b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change r * a < ‖r • x + z - z‖ ∧ ‖r • x + z - z‖ < r * b
    rw [norm_affine_sub, abs_of_pos hr]
    exact ⟨mul_lt_mul_of_pos_left (by simpa only [sub_zero] using hx.1) hr,
      mul_lt_mul_of_pos_left (by simpa only [sub_zero] using hx.2) hr⟩
  · intro hy
    refine ⟨r⁻¹ • (y - z), ?_, ?_⟩
    · change a < ‖r⁻¹ • (y - z) - 0‖ ∧ ‖r⁻¹ • (y - z) - 0‖ < b
      simp only [sub_zero]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      rw [inv_mul_eq_div]
      exact ⟨(lt_div_iff₀ hr).2 (by simpa only [mul_comm] using hy.1),
        (div_lt_iff₀ hr).2 (by simpa only [mul_comm] using hy.2)⟩
    · simp [smul_smul, hr.ne']

theorem sphereDiam_smul {C : ℝ} (hC : 0 < C) (D : ContMetric d)
    (z : Rd d) (r : ℝ) :
    sphereDiam (D.smul C hC) z r = ENNReal.ofReal C * sphereDiam D z r := by
  unfold sphereDiam
  simp_rw [ContMetric.internal_smul hC]
  simp only [ENNReal.mul_iSup]

theorem acrossDist_smul {C : ℝ} (hC : 0 < C) (D : ContMetric d)
    (z : Rd d) (a b : ℝ) :
    acrossDist (D.smul C hC) z a b = ENNReal.ofReal C * acrossDist D z a b := by
  unfold acrossDist
  simp_rw [ContMetric.smul_apply, ENNReal.ofReal_mul hC.le]
  simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top]

theorem sphereDiam_affine {r : ℝ} (hr : 0 < r) (z : Rd d)
    (D : ContMetric d) :
    sphereDiam (D.affine r hr.ne' z) 0 1 = sphereDiam D z r := by
  have hs := image_sphere_affine hr z 1
  simp only [mul_one] at hs
  have ha := image_ann_affine hr z (1 / 2) 2
  unfold sphereDiam
  rw [← hs]
  simp only [iSup_image]
  simp_rw [ContMetric.internal_affine hr.ne' z D]
  simp only [mul_one]
  rw [ha]
  congr 1
  ring

theorem acrossDist_affine {r : ℝ} (hr : 0 < r) (z : Rd d)
    (D : ContMetric d) (a b : ℝ) :
    acrossDist (D.affine r hr.ne' z) 0 a b = acrossDist D z (r * a) (r * b) := by
  unfold acrossDist
  rw [← image_sphere_affine hr z a, ← image_sphere_affine hr z b]
  simp only [iInf_image]
  rfl

end HigherDimLQGMetric
