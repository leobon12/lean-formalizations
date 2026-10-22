import HigherDimLQGMetric.Trunc.TailWeight
import HigherDimLQGMetric.ConvField.RadialWeightIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The scaled radial tail vanishes by dominated convergence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

def l2c_tailIntegrand (κ : Rd d → ℝ) (ε s : ℝ) : ℝ :=
  s ^ (d - 1) * |convKernel κ (s • e₁ d)| * l2c_tailWeight (d := d) ε s

theorem l2c_continuousOn_tailIntegrand (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (l2c_tailIntegrand κ ε) (Ioi (0 : ℝ)) := by
  have hK : Continuous (fun s : ℝ => convKernel κ (s • e₁ d)) :=
    (convKernel_contDiff (by omega : 0 < d) hκ).continuous.comp
      (continuous_id.smul continuous_const)
  have hb : Continuous (fun s : ℝ =>
      radBump (d := d) (Real.sqrt ε / 2) (Real.sqrt ε) ((ε * s) • e₁ d)) :=
    (contDiff_radBump (by positivity)
      (by have hp := Real.sqrt_pos.2 hε; linarith)).continuous.comp
        ((continuous_const.mul continuous_id).smul continuous_const)
  have hw : ContinuousOn (fun s : ℝ => l2b_growthWeight (ε * s)) (Ioi 0) := by
    exact l2b_continuousOn_growthWeight.comp
      (continuous_const.mul continuous_id).continuousOn
      (fun s hs => mul_pos hε hs)
  change ContinuousOn (fun s : ℝ =>
    s ^ (d - 1) * |convKernel κ (s • e₁ d)| *
      ((1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε) ((ε * s) • e₁ d)) *
        l2b_growthWeight (ε * s))) (Ioi 0)
  have hconst : Continuous (fun _ : ℝ => (1 : ℝ)) := continuous_const
  have hcont : ContinuousOn (fun s : ℝ =>
      s ^ (d - 1) * |convKernel κ (s • e₁ d)| *
        (1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε) ((ε * s) • e₁ d)) *
          l2b_growthWeight (ε * s)) (Ioi 0) :=
    ((((continuous_id.pow (d - 1)).mul hK.abs).mul
      (hconst.sub hb)).continuousOn.mul hw)
  convert hcont using 1
  funext s
  ring

theorem l2c_integrable_tailIntegrand (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) :
    IntegrableOn (l2c_tailIntegrand κ ε) (Ioi (0 : ℝ)) := by
  have hbase := l2b_integrable_radial_growth_kernel hd hκ (ε := 1) one_pos
  have he : (fun s : ℝ => s ^ (d - 1) *
      convKernelEps κ 1 (s • e₁ d) * l2b_growthWeight s) =
      fun s => s ^ (d - 1) * convKernel κ (s • e₁ d) * l2b_growthWeight s := by
    funext s
    simp [convKernelEps]
  rw [he] at hbase
  have hmeas : AEStronglyMeasurable (l2c_tailIntegrand κ ε)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (l2c_continuousOn_tailIntegrand hd hκ hε).aestronglyMeasurable measurableSet_Ioi
  apply (hbase.norm.const_mul 4).mono' hmeas
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have hp : 0 ≤ s ^ (d - 1) := pow_nonneg hs.le _
  have htw : 0 ≤ l2c_tailWeight (d := d) ε s := l2c_tailWeight_nonneg ε s
  have hw : 0 ≤ l2b_growthWeight s := by
    unfold l2b_growthWeight
    exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
  have hta := l2c_tailWeight_le hd hε hεsmall hs
  simp only [l2c_tailIntegrand, Real.norm_eq_abs, abs_mul, abs_of_nonneg hp,
    abs_of_nonneg htw, abs_of_nonneg hw, abs_abs]
  calc
    s ^ (d - 1) * |convKernel κ (s • e₁ d)| * l2c_tailWeight ε s
      ≤ s ^ (d - 1) * |convKernel κ (s • e₁ d)| *
          (4 * l2b_growthWeight s) := by gcongr
    _ = 4 * (s ^ (d - 1) * |convKernel κ (s • e₁ d)| *
        l2b_growthWeight s) := by ring

theorem l2c_tendsto_tail_integral (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Tendsto (fun ε : ℝ => ∫ s in Ioi (0 : ℝ), l2c_tailIntegrand κ ε s)
      (𝓝[>] 0) (𝓝 0) := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let B : ℝ → ℝ := fun s =>
    4 * |s ^ (d - 1) * convKernel κ (s • e₁ d) * l2b_growthWeight s|
  have hBI : Integrable B ν := by
    have hbase := l2b_integrable_radial_growth_kernel hd hκ
      (ε := 1) one_pos
    have he : (fun s : ℝ => s ^ (d - 1) *
        convKernelEps κ 1 (s • e₁ d) * l2b_growthWeight s) =
        fun s => s ^ (d - 1) * convKernel κ (s • e₁ d) * l2b_growthWeight s := by
      funext s
      simp [convKernelEps]
    rw [he] at hbase
    exact hbase.norm.const_mul 4
  have hmeas : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (l2c_tailIntegrand κ ε) ν := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (l2c_continuousOn_tailIntegrand hd hκ hε).aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ᵐ s ∂ν, ‖l2c_tailIntegrand κ ε s‖ ≤ B s := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with ε hε
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hp : 0 ≤ s ^ (d - 1) := pow_nonneg hs.le _
    have htw : 0 ≤ l2c_tailWeight (d := d) ε s := l2c_tailWeight_nonneg ε s
    have hw : 0 ≤ l2b_growthWeight s := by
      unfold l2b_growthWeight
      exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
    have hta := l2c_tailWeight_le hd hε.1 hε.2.le hs
    dsimp [l2c_tailIntegrand, B]
    simp only [abs_mul, abs_of_nonneg hp,
      abs_of_nonneg htw, abs_of_nonneg hw, abs_abs]
    calc
      s ^ (d - 1) * |convKernel κ (s • e₁ d)| * l2c_tailWeight ε s
        ≤ s ^ (d - 1) * |convKernel κ (s • e₁ d)| *
            (4 * l2b_growthWeight s) := by gcongr
      _ = 4 * (s ^ (d - 1) * |convKernel κ (s • e₁ d)| *
          l2b_growthWeight s) := by ring
  have hlim : ∀ᵐ s ∂ν,
      Tendsto (fun ε : ℝ => l2c_tailIntegrand κ ε s) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have he := l2c_tailWeight_eventually_zero hd hs
    have he' : (fun ε : ℝ => l2c_tailIntegrand κ ε s) =ᶠ[𝓝[>] 0]
        fun _ => 0 := by
      filter_upwards [he] with ε hε
      simp [l2c_tailIntegrand, hε]
    exact Tendsto.congr' he'.symm tendsto_const_nhds
  simpa only [ν, integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence B hmeas hbound hBI hlim)

end HigherDimLQGMetric
