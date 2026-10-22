import HigherDimLQGMetric.ConvField.JointMain
import HigherDimLQGMetric.ConvField.RadialMain

/-! Centered compact truncations converge after averaging their centers over the unit sphere. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2b_abs_trunc_radial_le (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (T : DistRd d) (n : ℕ) (z : Rd d) {C : ℝ}
    (hg : ∀ r : ℝ, 0 < r → |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    |((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          l2b_axisFactor κ n (Real.log ε) r * sphereAvg T r z| ≤
      ((volume : Measure (Rd d)).toSphere univ).toReal * C *
        ∫ r in Ioi (0 : ℝ),
          |r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * l2b_growthWeight r| := by
  let B : ℝ → ℝ := fun r =>
    |r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * l2b_growthWeight r|
  have hBi : IntegrableOn B (Ioi (0 : ℝ)) :=
    (l2b_integrable_radial_growth_kernel hd hκ hε).norm
  have hnorm : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖r ^ (d - 1) * l2b_axisFactor κ n (Real.log ε) r * sphereAvg T r z‖ ≤ C * B r := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_)
    have hp : 0 ≤ r ^ (d - 1) := pow_nonneg hr.le _
    have hW : 0 ≤ l2b_growthWeight r :=
      (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
    have hcut0 := radialProfile_nonneg (((n : ℝ) + 1)⁻¹ • (r • e₁ d))
    have hcut1 := radialProfile_le_one (((n : ℝ) + 1)⁻¹ • (r • e₁ d))
    rw [Real.norm_eq_abs, l2b_axisFactor, Real.exp_log hε]
    dsimp [B]
    simp only [abs_mul, abs_of_nonneg hp, abs_of_nonneg hW, abs_of_nonneg hcut0]
    calc
      r ^ (d - 1) * (|convKernelEps κ ε (r • e₁ d)| *
          radialProfile d (((n : ℝ) + 1)⁻¹ • (r • e₁ d))) * |sphereAvg T r z| ≤
        r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| * |sphereAvg T r z| := by
          gcongr
          exact mul_le_of_le_one_right (abs_nonneg _) hcut1
      _ ≤ r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
          (C * l2b_growthWeight r) := by gcongr; exact hg r hr
      _ = C * (r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
          l2b_growthWeight r) := by ring
  have harea : 0 ≤ ((volume : Measure (Rd d)).toSphere univ).toReal :=
    ENNReal.toReal_nonneg
  have h := norm_integral_le_of_norm_le (hBi.const_mul C) hnorm
  rw [Real.norm_eq_abs, integral_const_mul] at h
  rw [abs_mul, abs_of_nonneg harea]
  exact (mul_le_mul_of_nonneg_left h harea).trans_eq (by ring)

theorem l2b_ae_tendsto_sphereMean_convTrunc (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ =>
        ∫ u : Rd d, h ω (convTrunc κ ε u n) ∂(unitSphereProb d)) atTop
        (𝓝 (∫ u : Rd d, convMollify κ ε (h ω) u ∂(unitSphereProb d))) := by
  filter_upwards [l2b_ae_convMollify_tendsto d hd κ hκ P h hh,
    l2b_ae_convTrunc_radial_all hd hκ hh, l2b_ae_growth_all hd hh,
    l2b_ae_convMollify_continuousOn d hd κ hκ P h hh]
    with ω hlim hrad hgrowth hcont
  intro ε hε
  obtain ⟨C, hC, hCg⟩ := hgrowth 2
  let B : ℝ := ((volume : Measure (Rd d)).toSphere univ).toReal * C *
    ∫ r in Ioi (0 : ℝ),
      |r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * l2b_growthWeight r|
  have hBc : Integrable (fun _ : Rd d => B) (unitSphereProb d) := integrable_const _
  have hFm (n : ℕ) : AEStronglyMeasurable
      (fun u : Rd d => h ω (convTrunc κ ε u n)) (unitSphereProb d) := by
    have hc := (h ω).continuous.comp
      ((l2b_continuous_convTrunc_exp hd hκ n).comp
        ((continuous_const : Continuous fun _ : Rd d => Real.log ε).prodMk
          continuous_id))
    convert (hc.aestronglyMeasurable (μ := unitSphereProb d)) using 1
    funext u
    simp only [Function.comp_apply, Real.exp_log hε, id_eq]
    rfl
  have hbound (n : ℕ) : ∀ᵐ u ∂(unitSphereProb d),
      ‖h ω (convTrunc κ ε u n)‖ ≤ B := by
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    have hub : u ∈ closedBall (0 : Rd d) 2 := by
      rw [mem_closedBall, dist_zero_right, hu]
      norm_num
    rw [Real.norm_eq_abs, hrad ε hε u n]
    exact l2b_abs_trunc_radial_le hd hκ hε (h ω) n u (hCg u hub)
  have hlim' : ∀ᵐ u ∂(unitSphereProb d),
      Tendsto (fun n : ℕ => h ω (convTrunc κ ε u n)) atTop
        (𝓝 (convMollify κ ε (h ω) u)) := by
    apply ae_of_all
    intro u
    have ht := hlim ε hε u
    rwa [l2b_convMollify_eq_of_tendsto ht]
  exact tendsto_integral_of_dominated_convergence (fun _ : Rd d => B)
    hFm hBc hbound hlim'

end HigherDimLQGMetric
