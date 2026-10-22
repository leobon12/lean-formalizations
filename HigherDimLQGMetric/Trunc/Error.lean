import HigherDimLQGMetric.Trunc.TailIntegral
import HigherDimLQGMetric.ConvField.Scaling

/-! Deterministic radial identity for the full and localized fields. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2c_radial_error_scaled (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (T : DistRd d) (z : Rd d)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg T p.1 p.2)
      (Ioi 0 ×ˢ univ))
    (hgrowth : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    (∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        convKernelEps κ ε (r • e₁ d) * sphereAvg T r z) -
      (∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        (convKernelEps κ ε (r • e₁ d) *
          radBump (Real.sqrt ε / 2) (Real.sqrt ε) (r • e₁ d)) *
        sphereAvg T r z) =
      ∫ s in Ioi (0 : ℝ), s ^ (d - 1) * convKernel κ (s • e₁ d) *
        ((1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε)
          ((ε * s) • e₁ d)) * sphereAvg T (ε * s) z) := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let A : ℝ → ℝ := fun r => r ^ (d - 1) *
    convKernelEps κ ε (r • e₁ d) * sphereAvg T r z
  let ψ : ℝ → ℝ := fun r =>
    radBump (Real.sqrt ε / 2) (Real.sqrt ε) (r • e₁ d)
  have hAI : Integrable A ν := l2b_integrable_radial_sphereAvg hd hκ hε T z hcont hgrowth
  have hψc : Continuous ψ :=
    (contDiff_radBump (by positivity)
      (by have hp := Real.sqrt_pos.2 hε; linarith)).continuous.comp
        (continuous_id.smul continuous_const)
  have hψb : ∀ᵐ r ∂ν, ‖ψ r‖ ≤ 1 := by
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (l2c_radBump_mem_Icc _ _ _).1]
    exact (l2c_radBump_mem_Icc _ _ _).2
  have hAψI : Integrable (fun r => A r * ψ r) ν :=
    hAI.mul_bdd hψc.aestronglyMeasurable hψb
  have hfirst : (∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        (convKernelEps κ ε (r • e₁ d) * ψ r) * sphereAvg T r z) =
      ∫ r, A r * ψ r ∂ν := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp [A]
    ring
  have hsub : (∫ r, A r ∂ν) - (∫ r, A r * ψ r ∂ν) =
      ∫ r, A r * ((1 - ψ r)) ∂ν := by
    rw [← integral_sub hAI hAψI]
    congr 1
    funext r
    ring
  have hscale : (∫ r, A r * (1 - ψ r) ∂ν) =
      ∫ s in Ioi (0 : ℝ), s ^ (d - 1) * convKernel κ (s • e₁ d) *
        ((1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε)
          ((ε * s) • e₁ d)) * sphereAvg T (ε * s) z) := by
    have hρ : 0 < ε⁻¹ := inv_pos.mpr hε
    have hs := l2b_radial_integral_scale (κ := κ) hd
      (ε := 1) (ρ := ε⁻¹) one_pos hρ
      (fun r => (1 - ψ r) * sphereAvg T r z)
      (fun s => (1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε)
        ((ε * s) • e₁ d)) * sphereAvg T (ε * s) z)
      (by
        intro r hr
        have he : ε * (ε⁻¹ * r) = r := by field_simp
        simp only [he, ψ])
    have hs' := hs
    simp only [one_div, inv_inv, convKernelEps, Real.one_rpow,
      inv_one, one_smul, one_mul] at hs'
    convert hs' using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp [A, ψ, convKernelEps]
    ring
  rw [hfirst]
  change (∫ r, A r ∂ν) - (∫ r, A r * ψ r ∂ν) = _
  exact hsub.trans hscale

theorem l2c_abs_scaled_error_le (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (T : DistRd d) (z : Rd d) {C : ℝ}
    (hC : ∀ r : ℝ, 0 < r →
      |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    |∫ s in Ioi (0 : ℝ), s ^ (d - 1) * convKernel κ (s • e₁ d) *
      ((1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε)
        ((ε * s) • e₁ d)) * sphereAvg T (ε * s) z)| ≤
      C * ∫ s in Ioi (0 : ℝ), l2c_tailIntegrand κ ε s := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let G : ℝ → ℝ := fun s => s ^ (d - 1) * convKernel κ (s • e₁ d) *
    ((1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε)
      ((ε * s) • e₁ d)) * sphereAvg T (ε * s) z)
  have hTI := l2c_integrable_tailIntegrand hd hκ hε hεsmall
  have hbound : ∀ᵐ s ∂ν, ‖G s‖ ≤ C * l2c_tailIntegrand κ ε s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hp : 0 ≤ s ^ (d - 1) := pow_nonneg hs.le _
    have hb := l2c_radBump_mem_Icc (Real.sqrt ε / 2) (Real.sqrt ε)
      ((ε * s) • e₁ d)
    have hb0 : 0 ≤ 1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε)
        ((ε * s) • e₁ d) := sub_nonneg.2 hb.2
    have hr := hC (ε * s) (mul_pos hε hs)
    dsimp [G, l2c_tailIntegrand, l2c_tailWeight]
    simp only [abs_mul, abs_of_nonneg hp, abs_of_nonneg hb0]
    calc
      s ^ (d - 1) * |convKernel κ (s • e₁ d)| *
          ((1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε) ((ε * s) • e₁ d)) *
            |sphereAvg T (ε * s) z|)
        ≤ s ^ (d - 1) * |convKernel κ (s • e₁ d)| *
          ((1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε) ((ε * s) • e₁ d)) *
            (C * l2b_growthWeight (ε * s))) := by gcongr
      _ = C * (s ^ (d - 1) * |convKernel κ (s • e₁ d)| *
          ((1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε) ((ε * s) • e₁ d)) *
            l2b_growthWeight (ε * s))) := by ring
  have hi := norm_integral_le_of_norm_le (hTI.const_mul C) hbound
  simpa only [Real.norm_eq_abs, integral_const_mul] using hi

end HigherDimLQGMetric
