import HigherDimLQGMetric.ConvField.GrowthWeight

/-! Compact radial factors and their parameter continuity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

def l2b_axisFactor (κ : Rd d → ℝ) (n : ℕ) (u r : ℝ) : ℝ :=
  convKernelEps κ (Real.exp u) (r • e₁ d) *
    radialProfile d (((n : ℝ) + 1)⁻¹ • (r • e₁ d))

theorem l2b_continuous_axisFactor (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) :
    Continuous fun p : ℝ × ℝ => l2b_axisFactor κ n p.1 p.2 := by
  have he : Continuous fun p : ℝ × ℝ => Real.exp p.1 :=
    Real.continuous_exp.comp continuous_fst
  have hscale : Continuous fun p : ℝ × ℝ => Real.exp p.1 ^ (-(d : ℝ)) :=
    he.rpow_const (fun p => Or.inl (Real.exp_ne_zero _))
  have hinv : Continuous fun p : ℝ × ℝ => (Real.exp p.1)⁻¹ :=
    he.inv₀ (fun p => Real.exp_ne_zero _)
  have haxis : Continuous fun p : ℝ × ℝ => p.2 • e₁ d :=
    continuous_snd.smul continuous_const
  have harg : Continuous fun p : ℝ × ℝ => (Real.exp p.1)⁻¹ • (p.2 • e₁ d) :=
    hinv.smul haxis
  have hcut : Continuous fun p : ℝ × ℝ =>
      radialProfile d (((n : ℝ) + 1)⁻¹ • (p.2 • e₁ d)) :=
    (radialProfile d).contDiff.continuous.comp
      ((continuous_const : Continuous fun _ : ℝ × ℝ => ((n : ℝ) + 1)⁻¹).smul haxis)
  exact (hscale.mul ((convKernel_contDiff (by omega) hκ).continuous.comp harg)).mul hcut

theorem l2b_axisFactor_eq_zero (hd : 2 ≤ d)
    (n : ℕ) (u : ℝ) {r : ℝ} (hr : 2 * ((n : ℝ) + 1) ≤ r) :
    l2b_axisFactor κ n u r = 0 := by
  have hr0 : 0 ≤ r := by nlinarith
  have hscale : 2 ≤ ‖((n : ℝ) + 1)⁻¹ • (r • e₁ d)‖ := by
    simp only [norm_smul, HigherDimLFPP.norm_e₁ (by omega : 0 < d),
      mul_one, Real.norm_eq_abs, abs_of_nonneg hr0,
      abs_of_pos (inv_pos.2 (by positivity))]
    rw [abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (n : ℝ) + 1)), mul_comm]
    exact (le_mul_inv_iff₀ (by positivity : (0 : ℝ) < n + 1)).2 hr
  rw [l2b_axisFactor, radialProfile_eq_zero hscale, mul_zero]

end HigherDimLQGMetric
