import SupercriticalConformalCovariance.TV.RadialRepresentative

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Metric

namespace SupercriticalConformalCovariance.TV

def diskVarianceEnvelope (L S : ℝ) : ℝ :=
  -Real.log (1 - S ^ 2 / L ^ 2)

theorem diskVarianceEnvelope_mono_radius
    {L S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) (hSL : S < L)
    {y : ℂ} (hy : ‖y‖ ≤ S) :
    -Real.log (1 - ‖y‖ ^ 2 / L ^ 2) ≤ diskVarianceEnvelope L S := by
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
  have hS2 : S ^ 2 < L ^ 2 := by nlinarith [sq_nonneg S]
  have harg : 0 < 1 - S ^ 2 / L ^ 2 := by
    rw [sub_pos, div_lt_one hL2]
    exact hS2
  have hsq : ‖y‖ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
  have hcmp : 1 - S ^ 2 / L ^ 2 ≤ 1 - ‖y‖ ^ 2 / L ^ 2 := by
    exact sub_le_sub_left (div_le_div_of_nonneg_right hsq hL2.le) 1
  exact (neg_le_neg (Real.log_le_log harg hcmp))

theorem diskVarianceEnvelope_tendsto_zero
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) (S : ℝ) :
    Tendsto (fun n => diskVarianceEnvelope (L n) S) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hL
  have hfrac : Tendsto (fun n => S ^ 2 * ((L n)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (hinv.pow 2))
  have harg : Tendsto (fun n => 1 - S ^ 2 * ((L n)⁻¹) ^ 2) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub hfrac using 1 <;> norm_num
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
  convert hlog.neg using 1
  · ext n
    simp [diskVarianceEnvelope, Function.comp_def, div_eq_mul_inv, inv_pow]
  · norm_num

end SupercriticalConformalCovariance.TV
