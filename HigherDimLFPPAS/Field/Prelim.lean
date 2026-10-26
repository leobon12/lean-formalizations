import HigherDimLFPPAS.Signed.Radial
import HigherDimLFPPAS.Signed.Sec4

/-!
# Field estimates for Lemma 2.3

The first localization packet reuses the signed-seed radial formula and sphere-growth theorem to obtain the
pathwise logarithmic bound for the convolution field.  This file deliberately states the result for the canonical
pathwise field `convMollify`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open HigherDimLFPP (Rd e₁)
open HigherDimLQGMetric

namespace HigherDimLFPPAS.Field

variable {d : ℕ} {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- The radial representation of `h ∗ Kε`, on one event for every positive scale and every center.
This is the signed-seed copy of the host's pathwise radial formula. -/
theorem radial_formula_F1 (hd : 2 ≤ d) (hκ : IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      convMollify κ ε (h ω) z = sphArea d *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) *
          sphereAvg (h ω) r z := by
  filter_upwards [Signed.l2b_radial_seed d hd κ hκ P h hh] with ω hω
  intro ε hε z
  have harea : (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) = sphArea d := by
    dsimp [sphArea]
    exact (l2b_sphere_area d hd).symm
  rw [← harea]
  exact hω ε hε z

/- On one almost-sure event, `h ∗ Kε` has logarithmic growth on each compact ball, uniformly in
`ε ∈ (0,1]`.  The deterministic factor is the kernel's pinned radial growth moment. The imported pathwise radial
and growth estimates feed one measure-integral domination argument. -/
set_option maxHeartbeats 800000 in
theorem ae_convMollify_log_bound_F1 (hd : 2 ≤ d) (hκ : IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        |convMollify κ ε (h ω) z| ≤
          (sphArea d * l9bKernelMoment κ) * C * (1 + Real.log ε⁻¹) := by
  filter_upwards [radial_formula_F1 (d := d) hd hκ hh,
    l2b_ae_growth_all hd hh, hh.1.ae_continuousOn_sphereAvg hd] with ω hrad hgrowthAll hcont
  intro N
  obtain ⟨C, hC0, hC⟩ := hgrowthAll N
  refine ⟨C, hC0, ?_⟩
  intro z hz ε hε hε1
  have hφ := hrad ε hε z
  have hgrowthAtPoint : ∀ r : ℝ, 0 < r →
      |sphereAvg (h ω) r z| ≤ C * l2b_growthWeight r := hC z hz
  have hint : IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      convKernelEps κ ε (r • e₁ d) * sphereAvg (h ω) r z) (Ioi 0) :=
    Signed.l2b_integrable_radial_sphereAvg_seed hd hκ hε (h ω) z hcont.2 hgrowthAll
  have hbound :
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        |convKernelEps κ ε (r • e₁ d)| * l2b_growthWeight r ≤
        (1 + Real.log ε⁻¹) * l9bKernelMoment κ := by
    have h := Signed.l9b_subst_growth_le_seed (d := d) (κ := κ) hd hκ hε hε1 le_rfl
    simpa only [mul_zero, l9bKernelMoment] using h
  have hmoment : 0 ≤ l9bKernelMoment κ := l9bKernelMoment_nonneg κ
  have hlog : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε, hε1⟩)
  have hmajor : IntegrableOn (fun r : ℝ => C * (r ^ (d - 1) *
      |convKernelEps κ ε (r • e₁ d)| * l2b_growthWeight r)) (Ioi 0) := by
    have hbase := Signed.l2b_integrable_radial_growth_kernel_seed (d := d) hd hκ hε
    have hbaseNorm : IntegrableOn (fun r : ℝ => ‖r ^ (d - 1) *
        convKernelEps κ ε (r • e₁ d) * l2b_growthWeight r‖) (Ioi 0) := hbase.norm
    have hbaseAbs : IntegrableOn (fun r : ℝ => r ^ (d - 1) *
        |convKernelEps κ ε (r • e₁ d)| * l2b_growthWeight r) (Ioi 0) := by
      refine hbaseNorm.congr_fun (fun r hr => ?_) measurableSet_Ioi
      have hrpow : 0 ≤ r ^ (d - 1) := pow_nonneg (le_of_lt hr) _
      have hG : 0 ≤ l2b_growthWeight r := l9b_growthWeight_nonneg r
      change |r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) *
        l2b_growthWeight r| = _
      rw [abs_mul, abs_mul, abs_of_nonneg hrpow, abs_of_nonneg hG]
    exact hbaseAbs.const_mul C
  have hpt : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * sphereAvg (h ω) r z‖ ≤
        C * (r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| * l2b_growthWeight r) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hp : 0 ≤ r ^ (d - 1) := pow_nonneg hr0.le _
    have hW : 0 ≤ l2b_growthWeight r := l9b_growthWeight_nonneg r
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hp]
    calc r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
          |sphereAvg (h ω) r z|
        ≤ r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
            (C * l2b_growthWeight r) := by gcongr; exact hgrowthAtPoint r hr0
      _ = C * (r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
            l2b_growthWeight r) := by ring
  have hnorm := norm_integral_le_of_norm_le hmajor hpt
  rw [Real.norm_eq_abs, integral_const_mul] at hnorm
  have harea : 0 ≤ sphArea d := sphArea_nonneg d
  calc |convMollify κ ε (h ω) z|
      = sphArea d * |∫ r in Ioi (0 : ℝ),
          r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * sphereAvg (h ω) r z| := by
            rw [hφ, abs_mul, abs_of_nonneg (sphArea_nonneg d)]
    _ ≤ sphArea d * (C * ∫ r in Ioi (0 : ℝ),
          r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| * l2b_growthWeight r) := by
            exact mul_le_mul_of_nonneg_left hnorm harea
    _ ≤ sphArea d * (C * ((1 + Real.log ε⁻¹) * l9bKernelMoment κ)) := by
          gcongr
    _ = (sphArea d * l9bKernelMoment κ) * C * (1 + Real.log ε⁻¹) := by ring

end HigherDimLFPPAS.Field
