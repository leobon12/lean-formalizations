import HigherDimLQGMetric.ConvField.Shifts

/-! A uniform polynomial envelope for convolution kernels on compact scale intervals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2b_continuous_kernelAxis_exp (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Continuous fun p : ℝ × ℝ => convKernelEps κ (Real.exp p.1) (p.2 • HigherDimLFPP.e₁ d) := by
  have he : Continuous fun p : ℝ × ℝ => Real.exp p.1 :=
    Real.continuous_exp.comp continuous_fst
  have hscale : Continuous fun p : ℝ × ℝ => Real.exp p.1 ^ (-(d : ℝ)) :=
    he.rpow_const (fun p => Or.inl (Real.exp_ne_zero _))
  have hinv : Continuous fun p : ℝ × ℝ => (Real.exp p.1)⁻¹ :=
    he.inv₀ (fun p => Real.exp_ne_zero _)
  have haxis : Continuous fun p : ℝ × ℝ => p.2 • HigherDimLFPP.e₁ d :=
    continuous_snd.smul continuous_const
  have harg : Continuous fun p : ℝ × ℝ =>
      (Real.exp p.1)⁻¹ • (p.2 • HigherDimLFPP.e₁ d) := hinv.smul haxis
  exact hscale.mul ((convKernel_contDiff (by omega) hκ).continuous.comp harg)

theorem l2b_exists_uniform_kernel_decay (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, a ≤ ε → ε ≤ b → ∀ x : Rd d,
      |convKernelEps κ ε x| ≤ M * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
  obtain ⟨C₀, hC₀⟩ := convKernel_decay hd hκ
  let C : ℝ := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC (x : Rd d) : |convKernel κ x| ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) :=
    (hC₀ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by positivity) _))
  let D : ℝ := max 1 b
  have hD1 : 1 ≤ D := le_max_left _ _
  have hbD : b ≤ D := le_max_right _ _
  have hD0 : 0 < D := by linarith
  let M : ℝ := a ^ (-(d : ℝ)) * C * (D⁻¹) ^ (-((d : ℝ) + 1))
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM0, fun ε hεa hεb x => ?_⟩
  have hε0 : 0 < ε := ha.trans_le hεa
  have hεD : ε ≤ D := hεb.trans hbD
  have hεinv : D⁻¹ ≤ ε⁻¹ := inv_anti₀ hε0 hεD
  have hDinv : D⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
  have hbase : D⁻¹ * (1 + ‖x‖) ≤ 1 + ‖ε⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε0)]
    have hnr : 0 ≤ ‖x‖ := norm_nonneg x
    nlinarith [mul_le_mul_of_nonneg_right hεinv hnr]
  have hbase0 : 0 < D⁻¹ * (1 + ‖x‖) := by positivity
  have hpow : (1 + ‖ε⁻¹ • x‖) ^ (-((d : ℝ) + 1)) ≤
      (D⁻¹) ^ (-((d : ℝ) + 1)) * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
    calc
      _ ≤ (D⁻¹ * (1 + ‖x‖)) ^ (-((d : ℝ) + 1)) :=
        Real.rpow_le_rpow_of_nonpos hbase0 hbase (by
          have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          linarith)
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  have hεpow : ε ^ (-(d : ℝ)) ≤ a ^ (-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha hεa (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
  rw [convKernelEps, abs_mul, abs_of_nonneg (Real.rpow_nonneg hε0.le _)]
  calc ε ^ (-(d : ℝ)) * |convKernel κ (ε⁻¹ • x)|
      ≤ ε ^ (-(d : ℝ)) * (C * (1 + ‖ε⁻¹ • x‖) ^ (-((d : ℝ) + 1))) := by
        gcongr
        exact hC _
    _ ≤ a ^ (-(d : ℝ)) * (C * ((D⁻¹) ^ (-((d : ℝ) + 1)) *
        (1 + ‖x‖) ^ (-((d : ℝ) + 1)))) := by
        gcongr
    _ = M * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by dsimp [M]; ring

end HigherDimLQGMetric
