import HigherDimLQGMetric.ConvField.CenteredGaussian
import HigherDimLQGMetric.ConvField.KernelUniform
import HigherDimLQGMetric.Kernel.CovMain
import HigherDimLQGMetric.ConvField.RadialEnvelope

/-!
# Covariance limit for the normalized convolution field

The compact centered test functions of L2b converge pointwise to the signed
convolution density. A common polynomial envelope permits passage through the
logarithmic covariance integral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

private theorem law_one_add_norm_le_mul {d : ℕ} (z w : Rd d) :
    1 + ‖w‖ ≤ (1 + ‖z‖) * (1 + ‖z - w‖) := by
  have h' : ‖w‖ ≤ ‖z - w‖ + ‖z‖ := by
    calc
      ‖w‖ = ‖z - (z - w)‖ := by congr 1; abel
      _ ≤ ‖z‖ + ‖z - w‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  nlinarith [norm_nonneg z, norm_nonneg (z - w)]

private theorem law_decay_shift {d : ℕ} (z w : Rd d) :
    (1 + ‖z - w‖) ^ (-((d : ℝ) + 1)) ≤
      (1 + ‖z‖) ^ ((d : ℝ) + 1) *
        (1 + ‖w‖) ^ (-((d : ℝ) + 1)) := by
  have hpos : 0 < 1 + ‖z - w‖ := by positivity
  have hz : 0 < 1 + ‖z‖ := by positivity
  have hw : 0 < 1 + ‖w‖ := by positivity
  have hp : 0 ≤ (d : ℝ) + 1 := by positivity
  have h := Real.rpow_le_rpow_of_nonpos hw (law_one_add_norm_le_mul z w)
    (neg_nonpos.mpr hp)
  rw [Real.mul_rpow hz.le hpos.le] at h
  have hcancel : (1 + ‖z‖) ^ ((d : ℝ) + 1) *
      (1 + ‖z‖) ^ (-((d : ℝ) + 1)) = 1 := by
    rw [← Real.rpow_add hz]
    simp
  calc
    (1 + ‖z - w‖) ^ (-((d : ℝ) + 1)) =
        (1 + ‖z‖) ^ ((d : ℝ) + 1) *
          ((1 + ‖z‖) ^ (-((d : ℝ) + 1)) *
            (1 + ‖z - w‖) ^ (-((d : ℝ) + 1))) := by rw [← mul_assoc, hcancel, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hz.le _)

private theorem law_kernel_shift_bound {d : ℕ} {κ : Rd d → ℝ} {ε M R : ℝ}
    (hM : 0 ≤ M) (hK : ∀ v, |convKernelEps κ ε v| ≤
      M * (1 + ‖v‖) ^ (-((d : ℝ) + 1)))
    {z : Rd d} (hz : ‖z‖ ≤ R) (w : Rd d) :
    |convKernelEps κ ε (z - w)| ≤
      M * (1 + R) ^ ((d : ℝ) + 1) * l2b_decayEnvelope d ‖w‖ := by
  have hp : 0 ≤ (d : ℝ) + 1 := by positivity
  have hzR : (1 + ‖z‖) ^ ((d : ℝ) + 1) ≤
      (1 + R) ^ ((d : ℝ) + 1) :=
    Real.rpow_le_rpow (by positivity) (by linarith) hp
  calc
    |convKernelEps κ ε (z - w)| ≤
        M * (1 + ‖z - w‖) ^ (-((d : ℝ) + 1)) := hK _
    _ ≤ M * ((1 + ‖z‖) ^ ((d : ℝ) + 1) *
        (1 + ‖w‖) ^ (-((d : ℝ) + 1))) := by
          gcongr
          exact law_decay_shift z w
    _ ≤ M * ((1 + R) ^ ((d : ℝ) + 1) *
        (1 + ‖w‖) ^ (-((d : ℝ) + 1))) := by gcongr
    _ = _ := by
      simp only [l2b_decayEnvelope, max_eq_left (norm_nonneg w)]
      ring

private theorem law_trunc_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε M R : ℝ} (hM : 0 ≤ M)
    (hK : ∀ v, |convKernelEps κ ε v| ≤
      M * (1 + ‖v‖) ^ (-((d : ℝ) + 1)))
    {z : Rd d} (hz : ‖z‖ ≤ R) (n : ℕ) (w : Rd d) :
    |convTrunc κ ε z n w| ≤
      M * (1 + R) ^ ((d : ℝ) + 1) * l2b_decayEnvelope d ‖w‖ := by
  rw [l2b_convTrunc_apply hd hκ, abs_mul]
  have hc0 := radialProfile_nonneg (((n : ℝ) + 1)⁻¹ • (w - z))
  have hc1 := radialProfile_le_one (((n : ℝ) + 1)⁻¹ • (w - z))
  rw [abs_of_nonneg hc0]
  exact (mul_le_of_le_one_right (abs_nonneg _) hc1).trans
    (law_kernel_shift_bound hM hK hz w)

private theorem law_decay_integrable (d : ℕ) :
    Integrable (fun w : Rd d => l2b_decayEnvelope d ‖w‖) := by
  have hi : Integrable (fun w : Rd d =>
      (1 + ‖w‖) ^ (-((d : ℝ) + 1))) := by
    apply integrable_one_add_norm (μ := volume)
    simp only [finrank_euclideanSpace_fin]
    norm_num
  simpa only [l2b_decayEnvelope, max_eq_left (norm_nonneg _)] using hi

private theorem law_decay_le_one (d : ℕ) (w : Rd d) :
    |l2b_decayEnvelope d ‖w‖| ≤ 1 := by
  simp only [l2b_decayEnvelope, max_eq_left (norm_nonneg w)]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · nlinarith [norm_nonneg w]
  · have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith

private theorem law_log_base_integrable (d : ℕ) (hd : 2 ≤ d) :
    Integrable (fun p : Rd d × Rd d =>
      l2b_decayEnvelope d ‖p.1‖ * l2b_decayEnvelope d ‖p.2‖ *
        (-Real.log ‖p.1 - p.2‖)) := by
  let F : Rd d → ℝ := fun w => l2b_decayEnvelope d ‖w‖
  have hF : Integrable F := law_decay_integrable d
  have hmF : Measurable F :=
    ((l2b_continuous_decayEnvelope d).comp continuous_norm).measurable
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsFiniteMeasure (posM F) := isFiniteMeasure_posM_of_integrable hF
  haveI : IsFiniteMeasure (posM (-F)) := isFiniteMeasure_posM_of_integrable hF.neg
  have hlog : HigherDimLFPP.LogPairable (posM F) (posM (-F))
      (posM F) (posM (-F)) :=
    logPairable_posM_of_logMoment hF hF hmF hmF
      (law_decay_le_one d) (law_decay_le_one d)
      (l2b_integrable_log_decayEnvelope d)
      (l2b_integrable_log_decayEnvelope d)
  exact integrable_logCovF_of_pairable hmF hmF hlog

private theorem law_mean_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε M R : ℝ} (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hK : ∀ v, |convKernelEps κ ε v| ≤
      M * (1 + ‖v‖) ^ (-((d : ℝ) + 1)))
    (hε : 0 < ε) (n : ℕ) (w : Rd d) :
    |l2b_meanTruncTest hd hκ hε n w| ≤
      M * (1 + R) ^ ((d : ℝ) + 1) * l2b_decayEnvelope d ‖w‖ := by
  haveI := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  rw [l2b_meanTruncTest_apply hd hκ hε n w]
  have hbound : ∀ᵐ u ∂(unitSphereProb d),
      ‖convTrunc κ ε u n w‖ ≤
        M * (1 + R) ^ ((d : ℝ) + 1) * l2b_decayEnvelope d ‖w‖ := by
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    simpa only [Real.norm_eq_abs] using
      law_trunc_bound hd hκ hM hK (hu ▸ hR) n w
  have h := norm_integral_le_of_norm_le_const hbound
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

private theorem law_centered_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε M R : ℝ} (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hK : ∀ v, |convKernelEps κ ε v| ≤
      M * (1 + ‖v‖) ^ (-((d : ℝ) + 1)))
    (hε : 0 < ε) {x : Rd d} (hx : ‖x‖ ≤ R) (n : ℕ) (w : Rd d) :
    |(l2b_centeredTruncTest hd hκ hε x n).1 w| ≤
      (2 * (M * (1 + R) ^ ((d : ℝ) + 1))) * l2b_decayEnvelope d ‖w‖ := by
  change |convTrunc κ ε x n w - l2b_meanTruncTest hd hκ hε n w| ≤ _
  calc
    _ ≤ |convTrunc κ ε x n w| + |l2b_meanTruncTest hd hκ hε n w| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (convTrunc κ ε x n w) 0 (l2b_meanTruncTest hd hκ hε n w)
    _ ≤ (M * (1 + R) ^ ((d : ℝ) + 1)) * l2b_decayEnvelope d ‖w‖ +
        (M * (1 + R) ^ ((d : ℝ) + 1)) * l2b_decayEnvelope d ‖w‖ := by
          gcongr
          · exact law_trunc_bound hd hκ hM hK hx n w
          · exact law_mean_bound hd hκ hM hR hK hε n w
    _ = _ := by ring

private theorem law_density_eq {d : ℕ} {κ : Rd d → ℝ} (ε : ℝ)
    (x w : Rd d) :
    l2b_centeredKernelDensity κ ε x w =
      measConv κ ε (Measure.dirac x) w -
        measConv κ ε (unitSphereProb d) w := by
  simp only [l2b_centeredKernelDensity, measConv, integral_dirac]
  rw [l2b_convKernelEps_radial ε (norm_sub_rev x w)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun u => l2b_convKernelEps_radial ε (norm_sub_rev u w)

private theorem law_decay_nonneg (d : ℕ) (w : Rd d) :
    0 ≤ l2b_decayEnvelope d ‖w‖ := by
  change 0 ≤ (1 + max ‖w‖ 0) ^ (-((d : ℝ) + 1))
  positivity

private theorem law_tendsto_log_product (d : ℕ) (hd : 2 ≤ d)
    (f g : ℕ → Rd d → ℝ) (F G : Rd d → ℝ)
    (hfmeas : ∀ n, Measurable (f n)) (hgmeas : ∀ n, Measurable (g n))
    {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ n w, |f n w| ≤ B * l2b_decayEnvelope d ‖w‖)
    (hgB : ∀ n w, |g n w| ≤ B * l2b_decayEnvelope d ‖w‖)
    (hfLim : ∀ w, (fun n => f n w) =ᶠ[atTop] fun _ => F w)
    (hgLim : ∀ w, (fun n => g n w) =ᶠ[atTop] fun _ => G w) :
    Tendsto (fun n : ℕ => ∫ p : Rd d × Rd d,
      f n p.1 * (-Real.log ‖p.1 - p.2‖) * g n p.2) atTop
      (𝓝 (∫ p : Rd d × Rd d,
        F p.1 * (-Real.log ‖p.1 - p.2‖) * G p.2)) := by
  let e : Rd d → ℝ := fun w => l2b_decayEnvelope d ‖w‖
  let H : Rd d × Rd d → ℝ := fun p =>
    B ^ 2 * |e p.1 * e p.2 * (-Real.log ‖p.1 - p.2‖)|
  have hHint : Integrable H :=
    ((law_log_base_integrable d hd).abs).const_mul (B ^ 2)
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun p : Rd d × Rd d =>
      f n p.1 * (-Real.log ‖p.1 - p.2‖) * g n p.2) := by
    have hf : Measurable (fun p : Rd d × Rd d => f n p.1) :=
      (hfmeas n).comp measurable_fst
    have hg : Measurable (fun p : Rd d × Rd d => g n p.2) :=
      (hgmeas n).comp measurable_snd
    have hl : Measurable (fun p : Rd d × Rd d =>
        -Real.log ‖p.1 - p.2‖) :=
      (Real.measurable_log.comp
        (measurable_norm.comp (measurable_fst.sub measurable_snd))).neg
    exact ((hf.mul hl).mul hg).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ p : Rd d × Rd d ∂volume,
      ‖f n p.1 * (-Real.log ‖p.1 - p.2‖) * g n p.2‖ ≤ H p := by
    refine ae_of_all _ fun p => ?_
    have h1 := hfB n p.1
    have h2 := hgB n p.2
    have he1 : 0 ≤ e p.1 := law_decay_nonneg d p.1
    have he2 : 0 ≤ e p.2 := law_decay_nonneg d p.2
    change |f n p.1 * (-Real.log ‖p.1 - p.2‖) * g n p.2| ≤
      B ^ 2 * |e p.1 * e p.2 * (-Real.log ‖p.1 - p.2‖)|
    calc
      |f n p.1 * (-Real.log ‖p.1 - p.2‖) * g n p.2| =
          |f n p.1| * |-Real.log ‖p.1 - p.2‖| * |g n p.2| := by
            simp only [abs_mul]
      _ ≤
          (B * l2b_decayEnvelope d ‖p.1‖) *
            |-Real.log ‖p.1 - p.2‖| *
            (B * l2b_decayEnvelope d ‖p.2‖) := by gcongr
      _ = B ^ 2 * |e p.1 * e p.2 * (-Real.log ‖p.1 - p.2‖)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg he1, abs_of_nonneg he2]
        dsimp [e]
        ring
  have hlim : ∀ᵐ p : Rd d × Rd d ∂volume,
      Tendsto (fun n => f n p.1 * (-Real.log ‖p.1 - p.2‖) * g n p.2)
        atTop (𝓝 (F p.1 * (-Real.log ‖p.1 - p.2‖) * G p.2)) := by
    refine ae_of_all _ fun p => ?_
    have he : (fun n => f n p.1 * (-Real.log ‖p.1 - p.2‖) * g n p.2) =ᶠ[atTop]
        fun _ => F p.1 * (-Real.log ‖p.1 - p.2‖) * G p.2 := by
      filter_upwards [hfLim p.1, hgLim p.2] with n hn hm
      rw [hn, hm]
    exact tendsto_const_nhds.congr' he.symm
  exact tendsto_integral_of_dominated_convergence H hmeas hHint hbound hlim

private theorem law_integrable_log_product (d : ℕ) (hd : 2 ≤ d)
    (f g : Rd d → ℝ) (hfmeas : Measurable f) (hgmeas : Measurable g)
    {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ w, |f w| ≤ B * l2b_decayEnvelope d ‖w‖)
    (hgB : ∀ w, |g w| ≤ B * l2b_decayEnvelope d ‖w‖) :
    Integrable (fun p : Rd d × Rd d =>
      f p.1 * (-Real.log ‖p.1 - p.2‖) * g p.2) := by
  have hmeas : Measurable (fun p : Rd d × Rd d =>
      f p.1 * (-Real.log ‖p.1 - p.2‖) * g p.2) := by
    have hf : Measurable (fun p : Rd d × Rd d => f p.1) :=
      hfmeas.comp measurable_fst
    have hg : Measurable (fun p : Rd d × Rd d => g p.2) :=
      hgmeas.comp measurable_snd
    have hl : Measurable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖) :=
      (Real.measurable_log.comp
        (measurable_norm.comp (measurable_fst.sub measurable_snd))).neg
    exact (hf.mul hl).mul hg
  have hmajor : Integrable (fun p : Rd d × Rd d =>
      B ^ 2 * |l2b_decayEnvelope d ‖p.1‖ *
        l2b_decayEnvelope d ‖p.2‖ * (-Real.log ‖p.1 - p.2‖)|) :=
    ((law_log_base_integrable d hd).abs).const_mul (B ^ 2)
  apply hmajor.mono' hmeas.aestronglyMeasurable
  refine ae_of_all _ fun p => ?_
  have h1 := hfB p.1
  have h2 := hgB p.2
  have hg1 := law_decay_nonneg d p.1
  have hg2 := law_decay_nonneg d p.2
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg1, abs_of_nonneg hg2]
  calc
    |f p.1| * |-Real.log ‖p.1 - p.2‖| * |g p.2| ≤
        (B * l2b_decayEnvelope d ‖p.1‖) *
          |-Real.log ‖p.1 - p.2‖| *
          (B * l2b_decayEnvelope d ‖p.2‖) := by gcongr
    _ = B ^ 2 *
        (l2b_decayEnvelope d ‖p.1‖ *
          l2b_decayEnvelope d ‖p.2‖ *
          |-Real.log ‖p.1 - p.2‖|) := by ring

private theorem law_bound_of_eventually {d : ℕ} (f : ℕ → Rd d → ℝ)
    (F : Rd d → ℝ) {B : ℝ}
    (hfB : ∀ n w, |f n w| ≤ B * l2b_decayEnvelope d ‖w‖)
    (hfLim : ∀ w, (fun n => f n w) =ᶠ[atTop] fun _ => F w)
    (w : Rd d) : |F w| ≤ B * l2b_decayEnvelope d ‖w‖ := by
  obtain ⟨n, hn⟩ := (hfLim w).exists
  simp only at hn
  rw [← hn]
  exact hfB n w

private theorem law_density_measurable {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ε : ℝ) (x : Rd d) :
    Measurable (l2b_centeredKernelDensity κ ε x) := by
  haveI := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have he : l2b_centeredKernelDensity κ ε x =
      fun w => measConv κ ε (Measure.dirac x) w -
        measConv κ ε (unitSphereProb d) w := by
    funext w
    exact law_density_eq ε x w
  rw [he]
  exact (measurable_measConv hd hκ ε (Measure.dirac x)).sub
    (measurable_measConv hd hκ ε (unitSphereProb d))

/-- The deterministic logarithmic covariance of L2b's compact test approximations
converges to the covariance of the convolution density. -/
theorem law_tendsto_centered_covariance (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (x y : Rd d) :
    Tendsto (fun n : ℕ => logCovRd
      (l2b_centeredTruncTest hd hκ hε x n).1
      (l2b_centeredTruncTest hd hκ hε y n).1) atTop
      (𝓝 (convLogCov κ ε (Measure.dirac x) (unitSphereProb d)
        (Measure.dirac y) (unitSphereProb d))) := by
  let R : ℝ := max 1 (max ‖x‖ ‖y‖)
  have hR : 1 ≤ R := le_max_left _ _
  have hx : ‖x‖ ≤ R :=
    (le_max_left ‖x‖ ‖y‖).trans (le_max_right 1 _)
  have hy : ‖y‖ ≤ R :=
    (le_max_right ‖x‖ ‖y‖).trans (le_max_right 1 _)
  obtain ⟨M, hM, hKall⟩ :=
    l2b_exists_uniform_kernel_decay hd hκ (a := ε) (b := ε) hε
  have hK (v : Rd d) : |convKernelEps κ ε v| ≤
      M * (1 + ‖v‖) ^ (-((d : ℝ) + 1)) := hKall ε le_rfl le_rfl v
  let B : ℝ := 2 * (M * (1 + R) ^ ((d : ℝ) + 1))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let f : ℕ → Rd d → ℝ := fun n => (l2b_centeredTruncTest hd hκ hε x n).1
  let g : ℕ → Rd d → ℝ := fun n => (l2b_centeredTruncTest hd hκ hε y n).1
  let F : Rd d → ℝ := l2b_centeredKernelDensity κ ε x
  let G : Rd d → ℝ := l2b_centeredKernelDensity κ ε y
  have hfm (n : ℕ) : Measurable (f n) :=
    (l2b_centeredTruncTest hd hκ hε x n).1.continuous.measurable
  have hgm (n : ℕ) : Measurable (g n) :=
    (l2b_centeredTruncTest hd hκ hε y n).1.continuous.measurable
  have hFm : Measurable F := law_density_measurable hd hκ ε x
  have hGm : Measurable G := law_density_measurable hd hκ ε y
  have hfB (n : ℕ) (w : Rd d) :
      |f n w| ≤ B * l2b_decayEnvelope d ‖w‖ :=
    law_centered_bound hd hκ hM hR hK hε hx n w
  have hgB (n : ℕ) (w : Rd d) :
      |g n w| ≤ B * l2b_decayEnvelope d ‖w‖ :=
    law_centered_bound hd hκ hM hR hK hε hy n w
  have hfLim (w : Rd d) : (fun n => f n w) =ᶠ[atTop] fun _ => F w :=
    l2b_centeredTruncTest_eventually_density hd hκ hε x w
  have hgLim (w : Rd d) : (fun n => g n w) =ᶠ[atTop] fun _ => G w :=
    l2b_centeredTruncTest_eventually_density hd hκ hε y w
  have hFi : Integrable (fun p : Rd d × Rd d =>
      F p.1 * (-Real.log ‖p.1 - p.2‖) * G p.2) :=
    law_integrable_log_product d hd F G hFm hGm hB
      (law_bound_of_eventually f F hfB hfLim)
      (law_bound_of_eventually g G hgB hgLim)
  have hni (n : ℕ) : Integrable (fun p : Rd d × Rd d =>
      f n p.1 * (-Real.log ‖p.1 - p.2‖) * g n p.2) :=
    law_integrable_log_product d hd (f n) (g n) (hfm n) (hgm n)
      hB (hfB n) (hgB n)
  have hlim := law_tendsto_log_product d hd f g F G hfm hgm hB
    hfB hgB hfLim hgLim
  have hn (n : ℕ) : logCovRd (f n) (g n) =
      ∫ p : Rd d × Rd d, f n p.1 * (-Real.log ‖p.1 - p.2‖) * g n p.2 := by
    rw [logCovRd, Measure.volume_eq_prod (Rd d) (Rd d), integral_prod _ (hni n)]
  have hF : convLogCov κ ε (Measure.dirac x) (unitSphereProb d)
      (Measure.dirac y) (unitSphereProb d) =
      ∫ p : Rd d × Rd d,
        F p.1 * (-Real.log ‖p.1 - p.2‖) * G p.2 := by
    rw [convLogCov, Measure.volume_eq_prod (Rd d) (Rd d), integral_prod _ hFi]
    simp_rw [show ∀ w, measConv κ ε (Measure.dirac x) w -
      measConv κ ε (unitSphereProb d) w = F w from fun w =>
        (law_density_eq ε x w).symm]
    simp_rw [show ∀ w, measConv κ ε (Measure.dirac y) w -
      measConv κ ε (unitSphereProb d) w = G w from fun w =>
        (law_density_eq ε y w).symm]
  simpa only [hn, ← hF, f, g] using hlim

end HigherDimLQGMetric
