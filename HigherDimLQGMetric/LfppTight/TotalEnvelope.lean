import HigherDimLQGMetric.LfppTight.KernelEnvelope
import HigherDimLQGMetric.Sphere.Mol

/-! Uniform positive envelope for the centered compact test of the sphere mean. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_massTrunc_abs_le {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) (n : ℕ) :
    |∫ w : Rd d, l2b_meanTruncTest hd hκ hε.1 n w| ≤
      ∫ w : Rd d, |convKernel κ w| := by
  let T : Rd d → ℝ := l2b_meanTruncTest hd hκ hε.1 n
  let A : ℝ := ∫ w : Rd d, |convKernel κ w|
  let lam : Measure (Rd d) := l6a_kernelEnvelope κ ε
  obtain ⟨hlam, hmass, _, _, _⟩ := l6a_kernelEnvelope_bounds hd hκ hε
  letI : IsFiniteMeasure lam := hlam
  have hTi : Integrable T := integrable_testOn _
  have hpos : (posM fun w : Rd d => |T w|).real univ =
      ∫ w : Rd d, |T w| :=
    l6a_posM_real_univ_of_integrable_nonneg hTi.abs (fun _ => abs_nonneg _)
  have hle : (posM fun w : Rd d => |T w|).real univ ≤ lam.real univ := by
    exact ENNReal.toReal_mono (by finiteness)
      (l6a_meanTrunc_measure_le_conv hd hκ hε.1 n univ)
  calc
    |∫ w : Rd d, T w| ≤ ∫ w : Rd d, |T w| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := T)
    _ = (posM fun w : Rd d => |T w|).real univ := hpos.symm
    _ ≤ lam.real univ := hle
    _ = A := hmass

theorem l6a_sphLaw_eta_bounds {d : ℕ} (hd : 2 ≤ d)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (∀ z : Rd d, ∀ s > 0,
      (sphLaw 1 (0 : Rd d) η).real (closedBall z s) ≤ (2 ^ d : ℝ) * s) ∧
    Integrable (fun z : Rd d => Real.log (2 + ‖z‖))
      (sphLaw 1 (0 : Rd d) η) ∧
    (∫ z : Rd d, Real.log (2 + ‖z‖) ∂(sphLaw 1 (0 : Rd d) η)) ≤
      Real.log 4 := by
  let μ : Measure (Rd d) := sphLaw 1 (0 : Rd d) η
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_sphLaw (by omega : 1 ≤ d) 1 0 η
  have hball (z : Rd d) (s : ℝ) (hs : 0 < s) :
      μ.real (closedBall z s) ≤ (2 ^ d : ℝ) * s := by
    have h := growthBound_sphLaw hd (by norm_num : (0 : ℝ) < 1)
      (0 : Rd d) η z s hs
    simpa only [div_one] using h.trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))
  have hnorm : ∀ᵐ z ∂μ, ‖z‖ ≤ 2 := by
    filter_upwards [ae_sphLaw_norm_le (d := d) 1 (0 : Rd d) η] with z hz
    simp only [norm_zero, zero_add, abs_one, abs_of_pos hη0] at hz
    linarith
  have hm : Integrable (fun z : Rd d => Real.log (2 + ‖z‖)) μ :=
    integrable_logWeight_of_ae_bounded μ hnorm
  have hbound : ∀ᵐ z ∂μ, Real.log (2 + ‖z‖) ≤ Real.log 4 := by
    filter_upwards [hnorm] with z hz
    exact Real.log_le_log (by positivity) (by linarith)
  have hle := integral_mono_ae hm (integrable_const (Real.log 4)) hbound
  refine ⟨hball, hm, ?_⟩
  simpa only [integral_const, probReal_univ, one_smul] using hle

end HigherDimLQGMetric
