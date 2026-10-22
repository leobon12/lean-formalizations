import HigherDimLQGMetric.Kernel.ConvKernelSymbol
import HigherDimLQGMetric.Kernel.ConvKernelParamIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The kernel symbol near the origin

This module develops the exact scaled integral identity in MA5 A2.4. It is a starting point
for the multivariable derivative bounds required for spatial decay of `convKernel`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The scaled average of the radial symbol density over the unit interval. -/
def symbolAverage (κ : Rd d → ℝ) (ρ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, symbolDensity κ (ρ * u)

/-- The smooth-factor candidate on the radial line in MA5 A2.4. -/
def symbolAuxLine (κ : Rd d → ℝ) (ρ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
      u ^ (d - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) ((ρ * u) • e₁ d)‖ ^ 2

/-- The smooth-factor candidate of MA5 A2.4 on Euclidean space. -/
def symbolAux (κ : Rd d → ℝ) (ζ : Rd d) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
      u ^ (d - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (u • ζ)‖ ^ 2

theorem symbolAux_eq_line (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ζ : Rd d) : symbolAux κ ζ = symbolAuxLine κ ‖ζ‖ := by
  unfold symbolAux symbolAuxLine
  apply intervalIntegral.integral_congr
  intro u _
  dsimp
  have hnorm : ‖u • ζ‖ = ‖(‖ζ‖ * u) • e₁ d‖ := by
    rw [norm_smul, norm_smul, HigherDimLFPP.norm_e₁ hd, mul_one]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg ζ)]
    ring
  rw [fourier_kernel_eq_of_norm_eq hκ.radial hnorm]

/-- Exact identity `G(ρ) = 1 - ρ ∫₀¹ f(ρu) du`, valid even for negative `ρ`. -/
theorem symbolSq_eq_one_sub_mul_average (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ρ : ℝ) :
    symbolSq κ ρ = 1 - ρ * symbolAverage κ ρ := by
  rw [symbolSq_eq_one_sub_integral hd hκ]
  have h := intervalIntegral.smul_integral_comp_mul_left
    (f := symbolDensity κ) ρ (a := (0 : ℝ)) (b := (1 : ℝ))
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [← h]
  rfl

/-- Factoring out the scale leaves the fixed-interval radial average. -/
theorem symbolAverage_eq_pow_mul_auxLine (κ : Rd d → ℝ) (ρ : ℝ) :
    symbolAverage κ ρ = ρ ^ (d - 1) * symbolAuxLine κ ρ := by
  unfold symbolAverage symbolAuxLine
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp
  unfold symbolDensity symbolIntegrand
  rw [mul_pow]
  ring

/-- The A2.4 identity on the radial line, with no restriction on the sign of `ρ`. -/
theorem symbolSq_eq_one_sub_pow_auxLine (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ρ : ℝ) :
    symbolSq κ ρ = 1 - ρ ^ d * symbolAuxLine κ ρ := by
  rw [symbolSq_eq_one_sub_mul_average hd hκ,
    symbolAverage_eq_pow_mul_auxLine κ ρ]
  congr 1
  calc
    ρ * (ρ ^ (d - 1) * symbolAuxLine κ ρ) =
        ρ ^ ((d - 1) + 1) * symbolAuxLine κ ρ := by rw [pow_succ]; ring
    _ = ρ ^ d * symbolAuxLine κ ρ := by rw [Nat.sub_add_cancel hd]

/-- The exact multivariable A2.4 factorization, prior to regularity bounds. -/
theorem kernelSymbol_sq_eq_one_sub_pow_aux (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ζ : Rd d) :
    symbolSq κ ‖ζ‖ = 1 - ‖ζ‖ ^ d * symbolAux κ ζ := by
  rw [symbolSq_eq_one_sub_pow_auxLine hd hκ, symbolAux_eq_line hd hκ]

/-- The scaled average has no singularity at the origin. -/
theorem symbolAux_continuous (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Continuous (symbolAux κ) := by
  let f : Rd d → ℝ → ℝ := fun ζ u =>
    (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
      u ^ (d - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (u • ζ)‖ ^ 2
  have hFour : Continuous (fun p : Rd d × ℝ =>
      𝓕 (fun x : Rd d => (κ x : ℂ)) (p.2 • p.1)) :=
    (continuous_fourier_kernel hκ).comp (continuous_snd.smul continuous_fst)
  have hf : Continuous f.uncurry := by
    change Continuous (fun p : Rd d × ℝ =>
      (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
        p.2 ^ (d - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (p.2 • p.1)‖ ^ 2)
    exact (continuous_const.mul (continuous_snd.pow _)).mul (hFour.norm.pow _)
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hf
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  convert hc using 1
  funext ζ
  simp only [symbolAux, f, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]

/-- The auxiliary in the exact A2.4 factorization is smooth on all of Euclidean space. -/
theorem symbolAux_contDiff (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symbolAux κ) := by
  let f : Rd d → ℝ → ℝ := fun ζ u =>
    (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
      u ^ (d - 1) *
      Complex.normSq (𝓕 (fun x : Rd d => (κ x : ℂ)) (u • ζ))
  have hFour : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Rd d × ℝ => 𝓕 (fun x : Rd d => (κ x : ℂ)) (p.2 • p.1)) := by
    have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (𝓕 (fun x : Rd d => (κ x : ℂ))) := by
      rw [← coe_fourier_kernelSchwartz hκ]
      exact (𝓕 (kernelSchwartz hκ)).smooth ⊤
    exact hh.comp (contDiff_snd.smul contDiff_fst)
  have hNormSq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Rd d × ℝ => Complex.normSq
        (𝓕 (fun x : Rd d => (κ x : ℂ)) (p.2 • p.1))) := by
    have hr := Complex.reCLM.contDiff.comp hFour
    have hi := Complex.imCLM.contDiff.comp hFour
    simpa only [Complex.normSq_apply, Function.comp_apply, pow_two,
      Complex.reCLM_apply, Complex.imCLM_apply] using (hr.pow 2).add (hi.pow 2)
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f.uncurry := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Rd d × ℝ =>
        (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
          p.2 ^ (d - 1) *
          Complex.normSq (𝓕 (fun x : Rd d => (κ x : ℂ)) (p.2 • p.1)))
    exact (contDiff_const.mul (contDiff_snd.pow _)).mul hNormSq
  have h := contDiff_setIntegral_Icc_of_contDiff f hf
  convert h using 1
  funext ζ
  simp only [symbolAux, f, Complex.normSq_eq_norm_sq,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]

/-- Every derivative of the smooth auxiliary is bounded on the closed unit ball. -/
theorem symbolAux_iteratedFDeriv_bounded (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (n : ℕ) : ∃ C : ℝ, ∀ ζ : Rd d, ‖ζ‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (symbolAux κ) ζ‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ n (symbolAux κ)) :=
    (symbolAux_contDiff hκ).continuous_iteratedFDeriv (by simp)
  have hb : Bornology.IsBounded
      ((iteratedFDeriv ℝ n (symbolAux κ)) '' Metric.closedBall (0 : Rd d) 1) :=
    ((isCompact_closedBall (0 : Rd d) 1).image hc).isBounded
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  exact ⟨C, fun ζ hζ => hC _ ⟨ζ, by simpa only [Metric.mem_closedBall, dist_zero_right] using hζ,
    rfl⟩⟩

/-- On a fixed neighborhood of zero, the A2.4 perturbation is at most one half. -/
theorem symbolAux_small_near_zero (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ ζ : Rd d, ‖ζ‖ < ρ →
      |‖ζ‖ ^ d * symbolAux κ ζ| ≤ 1 / 2 := by
  let p : Rd d → ℝ := fun ζ => ‖ζ‖ ^ d * symbolAux κ ζ
  have hp : ContinuousAt p 0 :=
    ((continuous_norm.pow d).mul (symbolAux_contDiff hκ).continuous).continuousAt
  have hp0 : p 0 = 0 := by simp [p, Nat.ne_of_gt hd]
  have he : ∀ᶠ ζ in 𝓝 (0 : Rd d), |p ζ| < 1 / 2 := by
    have h := hp.abs.eventually_lt
      (continuousAt_const : ContinuousAt (fun _ : Rd d => (1 / 2 : ℝ)) 0)
      (by norm_num [hp0])
    exact h
  rcases Metric.mem_nhds_iff.mp he with ⟨ε, hε, hball⟩
  refine ⟨min ε 1, lt_min hε (by norm_num), min_le_right ε 1, fun ζ hζ => ?_⟩
  have hz : ζ ∈ Metric.ball (0 : Rd d) ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using lt_of_lt_of_le hζ (min_le_left ε 1)
  exact le_of_lt (hball hz)

end HigherDimLQGMetric
