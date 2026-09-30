import QuantumZipper.Proofs.Thm18.A1RNodes
import QuantumZipper.Proofs.Zipper.XPCIdBasic
import QuantumZipper.Proofs.Zipper.XFlowEnergyE1Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1R2 (log-derivative): the deterministic part of the growth node `A1RGrowthStmt`

The smoothed witness of the unzipped field is
`F_t(z, ρ) = evalReg Y ((f_t⁻¹)_* fc(z, ρ)) + Q ∫ log |(f_t⁻¹)'| dfc(z, ρ)`. This file bounds the
second (deterministic) term: for a good driver, `t > 0`, `‖z‖ ≤ R`, `Im z ≤ √ρ`, `0 < ρ < 1`,
`|∫ log |(f_t⁻¹)'| dfc(z, ρ)| ≤ C (1 + |log ρ|)`.

* Pointwise (`abs_log_norm_deriv_fwdMapInv_le`): Schwarz–Pick for the reverse flow in both
  directions, `Im w / Im g(w) ≤ |g'(w)| ≤ Im g(w) / Im w` (`TwoPoint.norm_deriv_revMap_le`,
  `TwoPoint.le_norm_deriv_revMap`, with `f_t⁻¹ = R_{0,t}` on `ℍ`), and `Im w ≤ Im g(w) ≤ ‖w‖ + C`,
  give `|log |g'(w)|| ≤ 2 |log Im w| + log (R + C + 1)`.
* Integral (`integral_abs_log_im_fc_small`): scaling `u ↦ (u − Re z)/ρ` and
  `F1.integral_abs_log_im_fc_unif` give `∫ |log Im| dfc(z, ρ) ≤ (3/2) |log ρ| + 200 + log 2`.

Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18
namespace A1R2

open Thm18Asm

variable {W : ℝ → ℝ}

/-- Lower Schwarz–Pick bound for `f_t⁻¹`. -/
theorem le_norm_deriv_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ H) : z.im / (fwdMapInv W t z).im ≤ ‖deriv (fwdMapInv W t) z‖ := by
  rw [RegCont.deriv_fwdMapInv_eq hW hW0 ht hz,
    UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hz]
  exact TwoPoint.le_norm_deriv_revMap (RegCont.continuous_vRev hW t) hz ht

/-- **Pointwise log-derivative bound.** -/
theorem abs_log_norm_deriv_fwdMapInv_le (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {C R : ℝ} (hC : ∀ w ∈ H, ‖fwdMapInv W t w - w‖ ≤ C) {w : ℂ} (hw : w ∈ H)
    (hwR : ‖w‖ ≤ R) :
    |Real.log ‖deriv (fwdMapInv W t) w‖| ≤ 2 * |Real.log w.im| + |Real.log (R + C + 1)| := by
  set g := fwdMapInv W t w with hg
  have hw0 : 0 < w.im := hw
  have hg0 : 0 < g.im := RS.fwdMapInv_mem_H hW hW0 ht hw
  have hup := E6.XAreaPC.norm_deriv_fwdMapInv_le hW hW0 ht hw
  have hlo := le_norm_deriv_fwdMapInv hW hW0 ht hw
  rw [← hg] at hup hlo
  have hd0 : 0 < ‖deriv (fwdMapInv W t) w‖ := lt_of_lt_of_le (div_pos hw0 hg0) hlo
  -- `Im w ≤ Im g`
  have hwg : w.im ≤ g.im := by
    have h := hlo.trans hup
    rw [div_le_div_iff₀ hg0 hw0] at h
    nlinarith
  -- `Im g ≤ R + C`
  have hgR : g.im ≤ R + C + 1 := by
    have h1 := hC w hw
    rw [← hg] at h1
    have h2 : g.im ≤ ‖g‖ := Complex.im_le_norm g
    have h3 : ‖g‖ ≤ ‖w‖ + C := by
      have := norm_le_norm_add_norm_sub' g w
      linarith [norm_sub_rev g w]
    linarith
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC w hw)
  -- the two log bounds
  have hl1 : Real.log ‖deriv (fwdMapInv W t) w‖ ≤ Real.log g.im - Real.log w.im := by
    rw [← Real.log_div hg0.ne' hw0.ne']
    exact Real.log_le_log hd0 hup
  have hl2 : Real.log w.im - Real.log g.im ≤ Real.log ‖deriv (fwdMapInv W t) w‖ := by
    rw [← Real.log_div hw0.ne' hg0.ne']
    exact Real.log_le_log (div_pos hw0 hg0) hlo
  -- `|log Im g| ≤ |log Im w| + |log (R + C + 1)|`
  have hlg : |Real.log g.im| ≤ |Real.log w.im| + |Real.log (R + C + 1)| := by
    rcases le_or_gt g.im 1 with h1 | h1
    · have e1 : |Real.log g.im| = -Real.log g.im := abs_of_nonpos (Real.log_nonpos hg0.le h1)
      have e2 : |Real.log w.im| = -Real.log w.im :=
        abs_of_nonpos (Real.log_nonpos hw0.le (hwg.trans h1))
      have := Real.log_le_log hw0 hwg
      rw [e1, e2]
      linarith [abs_nonneg (Real.log (R + C + 1))]
    · have e1 : |Real.log g.im| = Real.log g.im := abs_of_pos (Real.log_pos h1)
      have := Real.log_le_log hg0 hgR
      rw [e1]
      linarith [abs_nonneg (Real.log w.im), le_abs_self (Real.log (R + C + 1))]
  rw [abs_le]
  constructor
  · linarith [le_abs_self (Real.log g.im), neg_abs_le (Real.log w.im)]
  · linarith [le_abs_self (Real.log g.im), neg_abs_le (Real.log w.im)]

/-- **`|log Im|` averaged over a small folded circle near `ℝ`.** -/
theorem integral_abs_log_im_fc_small {z : ℂ} (hz : z ∈ Hbar) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hzρ : z.im ≤ Real.sqrt ρ) :
    ∫ u, |Real.log u.im| ∂foldedCircle z ρ ≤
      3 / 2 * |Real.log ρ| + 200 + Real.log 2 := by
  have hz0 : 0 ≤ z.im := hz
  set e : ℂ := ((ρ⁻¹ : ℝ) : ℂ) * (z + ((-z.re : ℝ) : ℂ)) with he
  have hmap := ExactCl.foldedCircle_map_affine (e := z) (r := ρ) (β := z.re) hρ
  rw [inv_mul_cancel₀ hρ.ne'] at hmap
  have hre : e.re = 0 := by simp [he]
  have him : e.im = z.im / ρ := by simp [he]; ring
  have hsq : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hsq1 : Real.sqrt ρ < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hρ1
  have hρsq : ρ = Real.sqrt ρ * Real.sqrt ρ := (Real.mul_self_sqrt hρ.le).symm
  have hen : ‖e‖ ≤ 1 / Real.sqrt ρ := by
    refine (Complex.norm_le_abs_re_add_abs_im e).trans ?_
    rw [hre, him, abs_zero, zero_add, abs_of_nonneg (div_nonneg hz0 hρ.le),
      div_le_div_iff₀ hρ hsq]
    nlinarith
  have hlog : |Real.log ρ| = -Real.log ρ := abs_of_neg (Real.log_neg hρ hρ1)
  have hlog_sqrt : Real.log (Real.sqrt ρ) = Real.log ρ / 2 := by
    rw [Real.log_sqrt hρ.le]
  have hbd : |Real.log (‖e‖ + 1)| ≤ Real.log 2 + 1 / 2 * |Real.log ρ| := by
    have h1 : 1 ≤ ‖e‖ + 1 := by linarith [norm_nonneg e]
    rw [abs_of_nonneg (Real.log_nonneg h1)]
    have h2 : ‖e‖ + 1 ≤ 2 / Real.sqrt ρ := by
      have : 1 ≤ 1 / Real.sqrt ρ := by rw [le_div_iff₀ hsq]; linarith
      have e2 : 2 / Real.sqrt ρ = 1 / Real.sqrt ρ + 1 / Real.sqrt ρ := by ring
      linarith
    have h3 := Real.log_le_log (by linarith) h2
    rw [Real.log_div (by norm_num) hsq.ne', hlog_sqrt] at h3
    rw [hlog]
    linarith
  -- pointwise comparison with the rescaled circle
  have hpt : ∀ u : ℂ, |Real.log u.im| ≤
      |Real.log ρ| + |Real.log (ExactCl.affR z.re ρ u).im| := by
    intro u
    have hu : u.im = ρ * (ExactCl.affR z.re ρ u).im := by
      simp only [ExactCl.affR, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_im, zero_mul, add_zero]
      field_simp
    by_cases h0 : (ExactCl.affR z.re ρ u).im = 0
    · rw [hu, h0, mul_zero, Real.log_zero, abs_zero]; positivity
    · rw [hu, Real.log_mul hρ.ne' h0]
      exact abs_add_le _ _
  have hmeas : Measurable fun v : ℂ => |Real.log v.im| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp Complex.measurable_im)
  have hint1 : Integrable (fun v : ℂ => |Real.log v.im|) (foldedCircle e 1) :=
    (TwoPoint.integrable_log_im_foldedCircle e one_pos).abs
  have hint2 : Integrable (fun u => |Real.log (ExactCl.affR z.re ρ u).im|)
      (foldedCircle z ρ) := by
    have := (integrable_map_measure hmeas.aestronglyMeasurable
      (ExactCl.measurable_affR z.re ρ).aemeasurable).1 (by rw [hmap]; exact hint1)
    exact this
  have hint0 : Integrable (fun u : ℂ => |Real.log u.im|) (foldedCircle z ρ) :=
    (TwoPoint.integrable_log_im_foldedCircle z hρ).abs
  have hI : ∫ u, |Real.log (ExactCl.affR z.re ρ u).im| ∂foldedCircle z ρ =
      ∫ v, |Real.log v.im| ∂foldedCircle e 1 := by
    rw [← hmap, integral_map (ExactCl.measurable_affR z.re ρ).aemeasurable
      hmeas.aestronglyMeasurable]
  have hU := F1.integral_abs_log_im_fc_unif (d := e) (r := 1) (rl := 1) (R₀ := ‖e‖ + 1)
    one_pos le_rfl le_rfl
  rw [Real.sqrt_one, div_one] at hU
  calc ∫ u, |Real.log u.im| ∂foldedCircle z ρ
      ≤ ∫ u, (|Real.log ρ| + |Real.log (ExactCl.affR z.re ρ u).im|) ∂foldedCircle z ρ :=
        integral_mono hint0 ((integrable_const _).add hint2) hpt
    _ = |Real.log ρ| + ∫ v, |Real.log v.im| ∂foldedCircle e 1 := by
        rw [integral_add (integrable_const _) hint2, integral_const, hI]
        simp
    _ ≤ 3 / 2 * |Real.log ρ| + 200 + Real.log 2 := by linarith

end A1R2
end R18
end QuantumZipper
