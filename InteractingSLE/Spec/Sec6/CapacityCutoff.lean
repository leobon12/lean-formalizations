/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.CircleCutoff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Logarithmic capacity cutoffs at a point

Packet PROVE-SEC6-A (specification §6.1, proof of Aux. lemma 29, `source/spec/p145-192.md`,
pp. 164–165): the cutoffs `b_{j,r}`, equal to `1` on `|z − p_j| ≤ r`, `0` on `|z − p_j| ≥ R`, and
logarithmic in between, with `∫_ℂ |∇b_{j,r}|² = 2π/log(R/r)`.

We use the smooth profile `η = cutProfile` (`0` on `(−∞, 1]`, `1` on `[4, ∞)`) and `R = 1`:
`b_{p,r}(z) = η(1 + 3 log(1/|z − p|) / log(1/r))` (`logCutoff`), which is `1` for `|z − p| ≤ r`,
`0` for `|z − p| ≥ 1`, and has a continuous derivative `logCutoffDeriv` supported in the annulus
`r ≤ |z − p| ≤ 1` with `‖D b_{p,r}(z)‖ ≤ 3 D / (log(1/r) |z − p|)`, `D = sup |η'|`. (The energy
bound `∫_ℂ ‖D b_{p,r}‖² ≤ 18 π D² / log(1/r)` follows by polar coordinates about `p`; not yet
formalized.)
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real ENNReal

namespace InteractingSLE.Sec6

/-- The inner variable `s(z) = 1 + 3 log(1/|z − p|) / log(1/r)` (via `log |z − p|²`). -/
def logVar (p : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  1 + (2 * -Real.log r)⁻¹ * (3 * -Real.log (‖z - p‖ ^ 2))

/-- The derivative of `logVar p r` (used at `z ≠ p`). -/
def logVarDeriv (p : ℂ) (r : ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ := fderiv ℝ (logVar p r) z

/-- The logarithmic cutoff `b_{p,r}`. -/
def logCutoff (p : ℂ) (r : ℝ) (z : ℂ) : ℝ := if z = p then 1 else cutProfile (logVar p r z)

/-- Its derivative. -/
def logCutoffDeriv (p : ℂ) (r : ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  if z = p then 0 else deriv cutProfile (logVar p r z) • logVarDeriv p r z

variable {p : ℂ} {r : ℝ}

theorem logVar_eq_fun : logVar p r = fun x =>
    1 + (2 * -Real.log r)⁻¹ * (3 * (-fun x => Real.log (‖id x - p‖ ^ 2)) x) := by
  funext x; simp [logVar]

theorem hasFDerivAt_logVar_aux {z : ℂ} (hz : z ≠ p) :
    HasFDerivAt (logVar p r) ((2 * -Real.log r)⁻¹ • (3 : ℝ) • -((‖id z - p‖ ^ 2)⁻¹ •
      (2 : ℕ) • (innerSL ℝ (id z - p)).comp (ContinuousLinearMap.id ℝ ℂ))) z := by
  have h0 : ‖id z - p‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 hz))
  have h1 := ((hasFDerivAt_id z).sub_const p).norm_sq
  have h2 := (((h1.log h0).neg.const_mul (3 : ℝ)).const_mul (2 * -Real.log r)⁻¹).const_add (1 : ℝ)
  rw [logVar_eq_fun]
  exact h2

theorem hasFDerivAt_logVar {z : ℂ} (hz : z ≠ p) :
    HasFDerivAt (logVar p r) (logVarDeriv p r z) z :=
  (hasFDerivAt_logVar_aux hz).differentiableAt.hasFDerivAt

theorem norm_logVarDeriv_le {z : ℂ} (hz : z ≠ p) (hL : 0 < -Real.log r) :
    ‖logVarDeriv p r z‖ ≤ 3 / (-Real.log r * ‖z - p‖) := by
  have hpos : 0 < ‖z - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  rw [logVarDeriv, (hasFDerivAt_logVar_aux hz).fderiv]
  simp only [id]
  have hin : ‖(innerSL ℝ (z - p)).comp (ContinuousLinearMap.id ℝ ℂ)‖ ≤ ‖z - p‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      rw [innerSL_apply_norm]
      exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le)
  calc ‖(2 * -Real.log r)⁻¹ • (3 : ℝ) • -((‖z - p‖ ^ 2)⁻¹ •
        (2 : ℕ) • (innerSL ℝ (z - p)).comp (ContinuousLinearMap.id ℝ ℂ))‖
      ≤ (2 * -Real.log r)⁻¹ * (3 * ((‖z - p‖ ^ 2)⁻¹ * (2 * ‖z - p‖))) := by
        rw [norm_smul, norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by norm_num : (0 : ℝ) < 3),
          abs_of_pos (by positivity)]
        gcongr
        refine norm_nsmul_le.trans ?_
        push_cast
        exact mul_le_mul_of_nonneg_left hin (by norm_num)
    _ = 3 / (-Real.log r * ‖z - p‖) := by field_simp

theorem logVar_ge_four {z : ℂ} (hr0 : 0 < r) (hr1 : r < 1) (hz : z ≠ p) (hzr : ‖z - p‖ ≤ r) :
    4 ≤ logVar p r z := by
  have hL : 0 < -Real.log r := neg_pos.2 (Real.log_neg hr0 hr1)
  have hpos : 0 < ‖z - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have hlog : Real.log (‖z - p‖ ^ 2) ≤ 2 * Real.log r := by
    rw [Real.log_pow]
    push_cast
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hzr) (by norm_num)
  unfold logVar
  have hl : Real.log r ≠ 0 := (Real.log_neg hr0 hr1).ne
  have h3 : (2 * -Real.log r)⁻¹ * (3 * (2 * -Real.log r)) = 3 := by field_simp
  have h4 : (2 * -Real.log r)⁻¹ * (3 * (2 * -Real.log r)) ≤
      (2 * -Real.log r)⁻¹ * (3 * -Real.log (‖z - p‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

theorem logVar_le_one {z : ℂ} (hr0 : 0 < r) (hr1 : r < 1) (hz : 1 ≤ ‖z - p‖) :
    logVar p r z ≤ 1 := by
  have hL : 0 < -Real.log r := neg_pos.2 (Real.log_neg hr0 hr1)
  have hlog : 0 ≤ Real.log (‖z - p‖ ^ 2) := Real.log_nonneg (by nlinarith)
  unfold logVar
  have : (2 * -Real.log r)⁻¹ * (3 * -Real.log (‖z - p‖ ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

/-- `b_{p,r} = 1` on the closed disk of radius `r` about `p`. -/
theorem logCutoff_eq_one {z : ℂ} (hr0 : 0 < r) (hr1 : r < 1) (hzr : ‖z - p‖ ≤ r) :
    logCutoff p r z = 1 := by
  unfold logCutoff
  split_ifs with hz
  · rfl
  · exact cutProfile_eq_one (logVar_ge_four hr0 hr1 hz hzr)

theorem logCutoff_nonneg (z : ℂ) : 0 ≤ logCutoff p r z := by
  unfold logCutoff; split_ifs
  · exact zero_le_one
  · exact cutProfile_nonneg _

theorem logCutoff_le_one (z : ℂ) : logCutoff p r z ≤ 1 := by
  unfold logCutoff; split_ifs
  · exact le_rfl
  · exact cutProfile_le_one _

theorem hasFDerivAt_logCutoff (hr0 : 0 < r) (hr1 : r < 1) (z : ℂ) :
    HasFDerivAt (logCutoff p r) (logCutoffDeriv p r z) z := by
  by_cases hz : z = p
  · subst hz
    have h : logCutoff z r =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
      filter_upwards [ball_mem_nhds z hr0] with w hw
      exact logCutoff_eq_one hr0 hr1 (by rw [mem_ball, dist_eq_norm] at hw; exact hw.le)
    simp only [logCutoffDeriv, ↓reduceIte]
    exact (hasFDerivAt_const (1 : ℝ) z).congr_of_eventuallyEq h
  · have h : logCutoff p r =ᶠ[𝓝 z] fun w => cutProfile (logVar p r w) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      simp only [logCutoff, hw, ↓reduceIte]
    simp only [logCutoffDeriv, hz, ↓reduceIte]
    exact ((hasDerivAt_cutProfile _).comp_hasFDerivAt z (hasFDerivAt_logVar hz)).congr_of_eventuallyEq h

theorem logVar_gt_four {z : ℂ} (hr0 : 0 < r) (hr1 : r < 1) (hz : z ≠ p) (hzr : ‖z - p‖ < r) :
    4 < logVar p r z := by
  have hL : 0 < -Real.log r := neg_pos.2 (Real.log_neg hr0 hr1)
  have hl : Real.log r ≠ 0 := (Real.log_neg hr0 hr1).ne
  have hpos : 0 < ‖z - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have hlog : Real.log (‖z - p‖ ^ 2) < 2 * Real.log r := by
    rw [Real.log_pow]; push_cast
    exact mul_lt_mul_of_pos_left (Real.log_lt_log hpos hzr) (by norm_num)
  unfold logVar
  have h3 : (2 * -Real.log r)⁻¹ * (3 * (2 * -Real.log r)) = 3 := by field_simp
  have h4 : (2 * -Real.log r)⁻¹ * (3 * (2 * -Real.log r)) <
      (2 * -Real.log r)⁻¹ * (3 * -Real.log (‖z - p‖ ^ 2)) :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  linarith

theorem logVar_lt_one {z : ℂ} (hr0 : 0 < r) (hr1 : r < 1) (hz : 1 < ‖z - p‖) :
    logVar p r z < 1 := by
  have hL : 0 < -Real.log r := neg_pos.2 (Real.log_neg hr0 hr1)
  have hlog : 0 < Real.log (‖z - p‖ ^ 2) := Real.log_pos (by nlinarith)
  unfold logVar
  have : (2 * -Real.log r)⁻¹ * (3 * -Real.log (‖z - p‖ ^ 2)) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

/-- The derivative vanishes off the annulus `r ≤ |z − p| ≤ 1`. -/
theorem logCutoffDeriv_eq_zero {z : ℂ} (hr0 : 0 < r) (hr1 : r < 1)
    (hz : ‖z - p‖ < r ∨ 1 < ‖z - p‖) : logCutoffDeriv p r z = 0 := by
  unfold logCutoffDeriv
  split_ifs with hzp
  · rfl
  · rcases hz with hz | hz
    · rw [deriv_cutProfile_eq_zero_of_gt (logVar_gt_four hr0 hr1 hzp hz), zero_smul]
    · rw [deriv_cutProfile_eq_zero_of_lt (logVar_lt_one hr0 hr1 hz), zero_smul]

theorem norm_logCutoffDeriv_le {D : ℝ} (hD : ∀ s, |deriv cutProfile s| ≤ D) (hr0 : 0 < r)
    (hr1 : r < 1) {z : ℂ} (hz : z ≠ p) :
    ‖logCutoffDeriv p r z‖ ≤ D * (3 / (-Real.log r * ‖z - p‖)) := by
  have hL : 0 < -Real.log r := neg_pos.2 (Real.log_neg hr0 hr1)
  simp only [logCutoffDeriv, hz, ↓reduceIte]
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hD _) (norm_logVarDeriv_le hz hL) (norm_nonneg _)
    ((abs_nonneg _).trans (hD 0))

theorem continuous_logCutoffDeriv (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (logCutoffDeriv p r) := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z = p
  · subst hz
    refine (continuousAt_const (y := (0 : ℂ →L[ℝ] ℝ))).congr ?_
    filter_upwards [ball_mem_nhds z hr0] with w hw
    rw [mem_ball, dist_eq_norm] at hw
    exact (logCutoffDeriv_eq_zero hr0 hr1 (Or.inl hw)).symm
  · have heq : logCutoffDeriv p r =ᶠ[𝓝 z] fun w => deriv cutProfile (logVar p r w) •
        ((2 * -Real.log r)⁻¹ • (3 : ℝ) • -((‖w - p‖ ^ 2)⁻¹ •
          (2 : ℕ) • (innerSL ℝ (w - p)).comp (ContinuousLinearMap.id ℝ ℂ))) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      simp only [logCutoffDeriv, hw, ↓reduceIte, logVarDeriv, (hasFDerivAt_logVar_aux hw).fderiv, id]
    refine ContinuousAt.congr ?_ heq.symm
    have hlv : ContinuousAt (logVar p r) z := (hasFDerivAt_logVar hz).continuousAt
    have hne : ‖z - p‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 hz))
    have hcp : ContinuousAt (fun w => deriv cutProfile (logVar p r w)) z :=
      continuous_deriv_cutProfile.continuousAt.comp hlv
    have hinv : ContinuousAt (fun w : ℂ => (‖w - p‖ ^ 2)⁻¹) z :=
      ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2).continuousAt.inv₀ hne
    have hin : ContinuousAt (fun w : ℂ =>
        (innerSL ℝ (w - p)).comp (ContinuousLinearMap.id ℝ ℂ)) z := by
      have h1 : Continuous fun w : ℂ => innerSL ℝ (w - p) :=
        (innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)
      exact h1.continuousAt.clm_comp continuousAt_const
    have h2 : ContinuousAt (fun w : ℂ => (2 : ℕ) •
        (innerSL ℝ (w - p)).comp (ContinuousLinearMap.id ℝ ℂ)) z := hin.const_smul _
    have h3 : ContinuousAt (fun w : ℂ => -((‖w - p‖ ^ 2)⁻¹ • (2 : ℕ) •
        (innerSL ℝ (w - p)).comp (ContinuousLinearMap.id ℝ ℂ))) z := (hinv.smul h2).neg
    have h4 : ContinuousAt (fun w : ℂ => (2 * -Real.log r)⁻¹ • (3 : ℝ) • -((‖w - p‖ ^ 2)⁻¹ •
        (2 : ℕ) • (innerSL ℝ (w - p)).comp (ContinuousLinearMap.id ℝ ℂ))) z :=
      (continuousAt_const (y := (2 * -Real.log r)⁻¹)).smul
        ((continuousAt_const (y := (3 : ℝ))).smul h3)
    exact hcp.smul h4

end InteractingSLE.Sec6
