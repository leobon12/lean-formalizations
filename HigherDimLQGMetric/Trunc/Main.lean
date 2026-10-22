import HigherDimLQGMetric.Trunc.Error
import HigherDimLQGMetric.ConvField.RadialMain

/-!
# [1] Lemma 2.12: truncation of the convolution field

On each closed ball the sphere average has a common growth constant. The
scaled radial tail is independent of the center and tends to zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

set_option maxHeartbeats 1000000 in
theorem l2c_trunc : L2c_trunc := by
  intro d hd κ hκ Ω _ P _ h hh
  filter_upwards [l2b_radial d hd κ hκ P h hh,
    l2c_ae_trunc_radial_all hd hκ hh,
    hh.1.ae_continuousOn_sphereAvg hd,
    l2b_ae_growth_all hd hh] with ω hfull htrunc hcont hgrowth
  intro R hR
  obtain ⟨N, hN⟩ := exists_nat_gt R
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  let area : ℝ := ((volume : Measure (Rd d)).toSphere univ).toReal
  let mass : ℝ → ℝ := fun ε => ∫ s in Ioi (0 : ℝ), l2c_tailIntegrand κ ε s
  have hmass : Tendsto (fun ε => |area| * C * mass ε) (𝓝[>] 0) (𝓝 0) := by
    have ht := (l2c_tendsto_tail_integral hd hκ).const_mul (|area| * C)
    simpa only [mass, mul_zero, mul_assoc] using ht
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hev := hmass.eventually (gt_mem_nhds hδ)
  filter_upwards [hev, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)]
    with ε hεbound hε z hz
  have hzN : z ∈ closedBall (0 : Rd d) (N : ℝ) := by
    rw [mem_closedBall, dist_zero_right] at hz ⊢
    exact hz.trans (le_of_lt hN)
  have heq := l2c_radial_error_scaled hd hκ hε.1 (h ω) z hcont.2 hgrowth
  have hpoint : convMollify κ ε (h ω) z - truncMollify κ ε (h ω) z =
      area * (∫ s in Ioi (0 : ℝ), s ^ (d - 1) * convKernel κ (s • e₁ d) *
        ((1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε)
          ((ε * s) • e₁ d)) * sphereAvg (h ω) (ε * s) z)) := by
    rw [hfull ε hε.1 z, htrunc ε hε.1 z, ← l2b_sphere_area d hd]
    have hI : (∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        l2c_axisFactor κ (Real.log ε / 2) r * sphereAvg (h ω) r z) =
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          (convKernelEps κ ε (r • e₁ d) *
            radBump (Real.sqrt ε / 2) (Real.sqrt ε) (r • e₁ d)) *
          sphereAvg (h ω) r z := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      dsimp only
      rw [l2c_axisFactor_log hε.1]
    rw [hI, ← mul_sub]
    dsimp [area]
    congr 1
  have hbound := l2c_abs_scaled_error_le hd hκ hε.1 hε.2.le
    (h ω) z (fun r hr => hC z hzN r hr)
  have habs : |convMollify κ ε (h ω) z - truncMollify κ ε (h ω) z| ≤
      |area| * C * mass ε := by
    rw [hpoint, abs_mul]
    calc
      |area| * |∫ s in Ioi (0 : ℝ), s ^ (d - 1) * convKernel κ (s • e₁ d) *
          ((1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε)
            ((ε * s) • e₁ d)) * sphereAvg (h ω) (ε * s) z)|
        ≤ |area| * (C * mass ε) :=
          mul_le_mul_of_nonneg_left hbound (abs_nonneg area)
      _ = |area| * C * mass ε := by ring
  simpa only [Real.dist_eq, Pi.zero_apply, zero_sub, abs_neg] using
    lt_of_le_of_lt habs hεbound

end HigherDimLQGMetric
