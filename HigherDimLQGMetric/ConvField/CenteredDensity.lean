import HigherDimLQGMetric.ConvField.CenteredL2

/-! The centered convolution kernel density and its L² distribution pairing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- Density of `(δ_x - σ₁) * K_ε`, written with the normalized unit-sphere measure. -/
def l2b_centeredKernelDensity (κ : Rd d → ℝ) (ε : ℝ) (x w : Rd d) : ℝ :=
  convKernelEps κ ε (x - w) -
    ∫ u : Rd d, convKernelEps κ ε (u - w) ∂(unitSphereProb d)

theorem l2b_cutoff_one_uniform_sphere (w : Rd d) :
    ∀ᶠ n : ℕ in atTop, ∀ u : Rd d, ‖u‖ = 1 →
      radialProfile d (((n : ℝ) + 1)⁻¹ • (w - u)) = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖w‖ + 1)
  refine Filter.eventually_atTop.2 ⟨N, fun n hn u hu => radialProfile_eq_one ?_⟩
  have htri : ‖w - u‖ ≤ ‖w‖ + 1 := by
    calc
      ‖w - u‖ ≤ ‖w‖ + ‖u‖ := norm_sub_le _ _
      _ = _ := by rw [hu]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < n + 1)),
    ← div_eq_inv_mul]
  apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).2
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem l2b_meanTruncTest_eventually_kernel (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (w : Rd d) :
    (fun n : ℕ => l2b_meanTruncTest hd hκ hε n w) =ᶠ[atTop]
      fun _ => ∫ u : Rd d, convKernelEps κ ε (u - w) ∂(unitSphereProb d) := by
  filter_upwards [l2b_cutoff_one_uniform_sphere (d := d) w] with n hn
  rw [l2b_meanTruncTest_apply hd hκ hε n w]
  apply integral_congr_ae
  filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
  rw [l2b_convTrunc_apply hd hκ, hn u hu, mul_one]

theorem l2b_centeredTruncTest_eventually_density (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (x w : Rd d) :
    (fun n : ℕ => (l2b_centeredTruncTest hd hκ hε x n).1 w) =ᶠ[atTop]
      fun _ => l2b_centeredKernelDensity κ ε x w := by
  filter_upwards [l2b_cutoff_eventually_one (d := d) x w,
    l2b_meanTruncTest_eventually_kernel hd hκ hε w] with n hx hm
  change convTrunc κ ε x n w - l2b_meanTruncTest hd hκ hε n w = _
  rw [l2b_convTrunc_apply hd hκ, hx, mul_one, hm]
  rfl

/-- The distribution pairing with `(δ_x - σ₁) * K_ε` is the L² limit of its
mean-zero compact test approximations. Its value off the convergence event is immaterial. -/
def l2b_pairCenteredKernel (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (x : Rd d) (T : DistRd d) : ℝ :=
  limUnder atTop fun n : ℕ => T (l2b_centeredTruncTest hd hκ hε x n).1

theorem l2b_ae_pairCenteredKernel_eq_convMollifyNorm (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ x : Rd d,
      l2b_pairCenteredKernel hd hκ hε x (h ω) =
        convMollify κ ε (h ω) x -
          ∫ u : Rd d, convMollify κ ε (h ω) u ∂(unitSphereProb d) := by
  filter_upwards [l2b_ae_centeredTrunc_tendsto d hd κ hκ P h hh] with ω hω
  intro ε hε x
  exact (hω ε hε x).limUnder_eq

theorem l2b_pairCenteredKernel_L2_tendsto (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) (x : Rd d) :
    Tendsto (fun n : ℕ => ∫ ω,
      (h ω (l2b_centeredTruncTest hd hκ hε x n).1 -
        l2b_pairCenteredKernel hd hκ hε x (h ω)) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have he := l2b_ae_pairCenteredKernel_eq_convMollifyNorm d hd κ hκ P h hh
  have hI (n : ℕ) : (∫ ω,
      (h ω (l2b_centeredTruncTest hd hκ hε x n).1 -
        l2b_pairCenteredKernel hd hκ hε x (h ω)) ^ 2 ∂P) =
      ∫ ω, (h ω (l2b_centeredTruncTest hd hκ hε x n).1 -
        (convMollify κ ε (h ω) x -
          ∫ u : Rd d, convMollify κ ε (h ω) u ∂(unitSphereProb d))) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [hω ε hε x]
  simpa only [hI] using l2b_centeredTrunc_L2_tendsto d hd κ hκ P h hh hε x

end HigherDimLQGMetric
