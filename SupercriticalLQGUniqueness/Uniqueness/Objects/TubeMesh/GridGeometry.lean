import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh.Core
import LQGMetric.Papers.CONF.S3D112G2




 






set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

open LQGMetric.Blueprint (confSq)
open LQGMetric.CONF (confCtr SqAdj)

 

theorem dist_square_center_lt {ε : ℝ} (hε : 0 < ε) (k : ℤ × ℤ) {w : ℂ}
    (hw : w ∈ confSq ε 0 k) :
    dist w (confCtr ε 0 k) < 3 * ε / 4 := by
  rcases hw with ⟨hlo1, hhi1, hlo2, hhi2⟩
  simp only [Complex.zero_re, zero_add] at hlo1 hhi1
  simp only [Complex.zero_im, zero_add] at hlo2 hhi2
  have hre : -ε / 2 ≤ (w - confCtr ε 0 k).re ∧
      (w - confCtr ε 0 k).re ≤ ε / 2 := by
    simp only [Complex.sub_re, confCtr, Complex.zero_re]
    constructor <;> nlinarith [hlo1, hhi1]
  have him : -ε / 2 ≤ (w - confCtr ε 0 k).im ∧
      (w - confCtr ε 0 k).im ≤ ε / 2 := by
    simp only [Complex.sub_im, confCtr, Complex.zero_im]
    constructor <;> nlinarith [hlo2, hhi2]
  have hsre : (w - confCtr ε 0 k).re ^ 2 ≤ (ε / 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hre.2) (by linarith : 0 ≤ ε / 2 + (w - confCtr ε 0 k).re)]
  have hsim : (w - confCtr ε 0 k).im ^ 2 ≤ (ε / 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr him.2) (by linarith : 0 ≤ ε / 2 + (w - confCtr ε 0 k).im)]
  have hnorm : ‖w - confCtr ε 0 k‖ ^ 2 ≤ ε ^ 2 / 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (w - confCtr ε 0 k), sq_nonneg ε]

 
theorem dist_adjacent_centers {ε : ℝ} (hε : 0 < ε) {k k' : ℤ × ℤ}
    (h : SqAdj k k') :
    dist (confCtr ε 0 k) (confCtr ε 0 k') = ε := by
  have hreal : (((k'.1 - k.1 : ℤ) : ℝ) ^ 2 +
      ((k'.2 - k.2 : ℤ) : ℝ) ^ 2) = 1 := by
    exact_mod_cast h
  have hre : (confCtr ε 0 k - confCtr ε 0 k').re =
      -((k'.1 - k.1 : ℤ) : ℝ) * ε := by
    simp [confCtr]; ring
  have him : (confCtr ε 0 k - confCtr ε 0 k').im =
      -((k'.2 - k.2 : ℤ) : ℝ) * ε := by
    simp [confCtr]; ring
  have hnorm : ‖confCtr ε 0 k - confCtr ε 0 k'‖ ^ 2 = ε ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    nlinarith [hreal]
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (confCtr ε 0 k - confCtr ε 0 k')]


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh
