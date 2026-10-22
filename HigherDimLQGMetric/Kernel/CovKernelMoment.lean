import HigherDimLQGMetric.Kernel.CovKernelEps
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Logarithmic moments of the convolution kernel

The decay exponent `d+1` gives the logarithmic moment needed for the
unbounded convolution densities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

private theorem log_two_add_norm_le (x : Rd d) :
    Real.log (2 + ‖x‖) ≤
      4 * (1 + ‖x‖) ^ ((1 / 2 : ℝ)) := by
  have h := Real.log_le_rpow_div (x := 2 + ‖x‖) (by positivity)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hp : (2 + ‖x‖) ^ ((1 / 2 : ℝ)) ≤
      2 * (1 + ‖x‖) ^ ((1 / 2 : ℝ)) := by
    have hle : 2 + ‖x‖ ≤ 4 * (1 + ‖x‖) := by nlinarith [norm_nonneg x]
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 2 + ‖x‖) hle
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
      (by positivity : 0 ≤ 1 + ‖x‖)] at hr
    norm_num at hr ⊢
    exact hr
  calc
    Real.log (2 + ‖x‖) ≤ (2 + ‖x‖) ^ ((1 / 2 : ℝ)) / (1 / 2 : ℝ) := h
    _ = 2 * (2 + ‖x‖) ^ ((1 / 2 : ℝ)) := by ring
    _ ≤ 4 * (1 + ‖x‖) ^ ((1 / 2 : ℝ)) := by linarith

theorem integrable_logMoment_convKernel (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Integrable (fun x : Rd d =>
      Real.log (2 + ‖x‖) * convKernel κ x) := by
  obtain ⟨C, hC⟩ := convKernel_decay hd hκ
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbase : Integrable (fun x : Rd d =>
      4 * B * (1 + ‖x‖) ^ (-((d : ℝ) + 1 / 2))) := by
    have h : Integrable (fun x : Rd d =>
        (1 + ‖x‖) ^ (-((d : ℝ) + 1 / 2))) := by
      apply integrable_one_add_norm (μ := volume)
      simp only [finrank_euclideanSpace_fin]
      norm_num
    exact h.const_mul (4 * B)
  apply hbase.mono'
  · have hcont : Continuous (fun x : Rd d =>
        Real.log (2 + ‖x‖) * convKernel κ x) := by
      apply Continuous.mul
      · apply Continuous.log
        · fun_prop
        · intro x
          positivity
      · exact (convKernel_contDiff (by omega) hκ).continuous
    exact hcont.aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    have hr : 0 < 1 + ‖x‖ := by positivity
    have hlog : 0 ≤ Real.log (2 + ‖x‖) :=
      Real.log_nonneg (by nlinarith [norm_nonneg x])
    have hK : |convKernel κ x| ≤
        B * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) :=
      (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog]
    calc
      Real.log (2 + ‖x‖) * |convKernel κ x| ≤
          Real.log (2 + ‖x‖) *
            (B * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by gcongr
      _ ≤ (4 * (1 + ‖x‖) ^ ((1 / 2 : ℝ))) *
            (B * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by
          gcongr
          exact log_two_add_norm_le x
      _ = 4 * B * (1 + ‖x‖) ^ (-((d : ℝ) + 1 / 2)) := by
          calc
            _ = 4 * B * ((1 + ‖x‖) ^ ((1 / 2 : ℝ)) *
                (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by ring
            _ = _ := by
              rw [← Real.rpow_add hr]
              congr 1
              ring_nf

theorem integrable_logMoment_convKernelEps (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : Rd d =>
      Real.log (2 + ‖x‖) * convKernelEps κ ε x) := by
  let T : Rd d → Rd d := fun x => ε⁻¹ • x
  have hT : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hmain := ((integrable_logMoment_convKernel hd hκ).comp_smul hT).const_mul
    (ε ^ (-(d : ℝ)))
  have hplain := ((integrable_convKernel hd hκ).comp_smul hT).const_mul
    (Real.log (2 + ε) * ε ^ (-(d : ℝ)))
  apply (hmain.norm.add hplain.norm).mono'
  · have hc : Continuous (fun x : Rd d =>
        Real.log (2 + ‖x‖) * convKernelEps κ ε x) := by
      apply Continuous.mul
      · apply Continuous.log
        · fun_prop
        · intro x; positivity
      · exact continuous_const.mul
          ((convKernel_contDiff (by omega) hκ).continuous.comp
            (continuous_const_smul _))
    exact hc.aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    have he : x = ε • T x := by
      dsimp [T]
      rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
    have hnorm : ‖x‖ = ε * ‖T x‖ := by
      calc
        ‖x‖ = ‖ε • T x‖ := congrArg norm he
        _ = _ := by simp [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hp : 2 + ‖x‖ ≤ (2 + ε) * (2 + ‖T x‖) := by
      rw [hnorm]
      nlinarith [norm_nonneg (T x)]
    have hlog : Real.log (2 + ‖x‖) ≤
        Real.log (2 + ‖T x‖) + Real.log (2 + ε) := by
      rw [← Real.log_mul (by positivity : 2 + ‖T x‖ ≠ 0)
        (by positivity : 2 + ε ≠ 0)]
      rw [mul_comm]
      exact Real.log_le_log (by positivity) hp
    have h0 : 0 ≤ Real.log (2 + ‖x‖) :=
      Real.log_nonneg (by nlinarith [norm_nonneg x])
    have h0' : 0 ≤ Real.log (2 + ‖T x‖) + Real.log (2 + ε) := by
      apply add_nonneg
      · exact Real.log_nonneg (by nlinarith [norm_nonneg (T x)])
      · exact Real.log_nonneg (by linarith)
    have hs : 0 ≤ ε ^ (-(d : ℝ)) := Real.rpow_nonneg hε.le _
    change |Real.log (2 + ‖x‖) * (ε ^ (-(d : ℝ)) * convKernel κ (T x))| ≤
      |ε ^ (-(d : ℝ)) * (Real.log (2 + ‖T x‖) * convKernel κ (T x))| +
        |Real.log (2 + ε) * ε ^ (-(d : ℝ)) * convKernel κ (T x)|
    rw [abs_mul, abs_of_nonneg h0, abs_mul, abs_of_nonneg hs]
    calc
      Real.log (2 + ‖x‖) * (ε ^ (-(d : ℝ)) * |convKernel κ (T x)|) ≤
        (Real.log (2 + ‖T x‖) + Real.log (2 + ε)) *
          (ε ^ (-(d : ℝ)) * |convKernel κ (T x)|) := by gcongr
      _ = |ε ^ (-(d : ℝ)) * (Real.log (2 + ‖T x‖) * convKernel κ (T x))| +
            |Real.log (2 + ε) * ε ^ (-(d : ℝ)) * convKernel κ (T x)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_nonneg hs,
            abs_of_nonneg (Real.log_nonneg (by nlinarith [norm_nonneg (T x)])),
            abs_of_nonneg (Real.log_nonneg (by linarith : 1 ≤ 2 + ε))]
          ring

end HigherDimLQGMetric
