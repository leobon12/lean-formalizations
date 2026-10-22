import HigherDimLQGMetric.LfppTight.PosMLogMoment
import HigherDimLQGMetric.LfppTight.KernelLogUniform

/-! Uniform mass, growth, and logarithmic moment of the absolute convolution envelope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

def l6a_kernelEnvelope {d : ℕ} (κ : Rd d → ℝ) (ε : ℝ) : Measure (Rd d) :=
  Measure.conv (unitSphereProb d)
    (posM (fun w : Rd d => |convKernelEps κ ε w|))

theorem l6a_kernelEnvelope_bounds {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) :
    let A := ∫ w : Rd d, |convKernel κ w|
    let B := ∫ w : Rd d, |convKernel κ w| * Real.log (2 + ‖w‖)
    IsFiniteMeasure (l6a_kernelEnvelope κ ε) ∧
    (l6a_kernelEnvelope κ ε).real univ = A ∧
    (∀ z : Rd d, ∀ s > 0,
      (l6a_kernelEnvelope κ ε).real (closedBall z s) ≤
        (2 ^ d : ℝ) * A * s) ∧
    Integrable (fun z : Rd d => Real.log (2 + ‖z‖))
      (l6a_kernelEnvelope κ ε) ∧
    (∫ z : Rd d, Real.log (2 + ‖z‖) ∂(l6a_kernelEnvelope κ ε)) ≤
      A * Real.log 3 + B := by
  let μ : Measure (Rd d) := unitSphereProb d
  let f : Rd d → ℝ := fun w => |convKernelEps κ ε w|
  let ν : Measure (Rd d) := posM f
  let lam : Measure (Rd d) := l6a_kernelEnvelope κ ε
  let A : ℝ := ∫ w : Rd d, |convKernel κ w|
  let B : ℝ := ∫ w : Rd d, |convKernel κ w| * Real.log (2 + ‖w‖)
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_unitSphereProb (by omega : 1 ≤ d)
  have hfcont : Continuous f := by
    have hkcont : Continuous (convKernelEps κ ε) :=
      continuous_const.mul
        ((convKernel_contDiff (by omega : 0 < d) hκ).continuous.comp
          (continuous_const_smul _))
    exact hkcont.abs
  have hfi : Integrable f := (integrable_convKernelEps hd hκ hε.1).abs
  have hwfi : Integrable (fun x : Rd d => Real.log (2 + ‖x‖) * f x) := by
    have h := (integrable_logMoment_convKernelEps hd hκ hε.1).abs
    convert h using 1
    funext x
    dsimp [f]
    rw [abs_mul, abs_of_nonneg (Real.log_nonneg
      (by nlinarith [norm_nonneg x] : 1 ≤ 2 + ‖x‖))]
  letI : IsFiniteMeasure ν := isFiniteMeasure_posM_of_integrable hfi
  letI : IsFiniteMeasure lam :=
    show IsFiniteMeasure (Measure.conv μ ν) by infer_instance
  have hνmass : ν.real univ = A := by
    dsimp [ν, A, f]
    rw [l6a_posM_real_univ_of_integrable_nonneg hfi (fun _ => abs_nonneg _),
      ← l2b_integral_abs_convKernelEps_eq hε.1]
  have hνmoment : Integrable (fun x : Rd d => Real.log (2 + ‖x‖)) ν :=
    integrable_logWeight_posM hfcont.measurable hwfi
  have hνmoment_le : (∫ x : Rd d, Real.log (2 + ‖x‖) ∂ν) ≤ B := by
    rw [l6a_integral_logWeight_posM hfcont.measurable
      (fun _ => abs_nonneg _) hwfi]
    change (∫ x : Rd d, Real.log (2 + ‖x‖) * |convKernelEps κ ε x|) ≤ B
    have hcomm : (∫ x : Rd d,
      Real.log (2 + ‖x‖) * |convKernelEps κ ε x|) =
      ∫ x : Rd d, |convKernelEps κ ε x| * Real.log (2 + ‖x‖) := by
      congr 1
      funext x
      ring
    rw [hcomm]
    exact l6a_integral_abs_logKernelEps_le hd hκ hε
  have hμmoment : Integrable (fun x : Rd d => Real.log (2 + ‖x‖)) μ :=
    integrable_logWeight_of_ae_bounded μ (ae_unitSphereProb_norm_le d)
  have hμmoment_le : (∫ x : Rd d, Real.log (2 + ‖x‖) ∂μ) ≤
      Real.log 3 := by
    have hbound : ∀ᵐ x ∂μ, Real.log (2 + ‖x‖) ≤ Real.log 3 := by
      filter_upwards [ae_unitSphereProb_norm_le d] with x hx
      exact Real.log_le_log (by positivity) (by linarith)
    have ht := integral_mono_ae hμmoment (integrable_const (Real.log 3)) hbound
    simpa only [integral_const, probReal_univ, one_smul] using ht
  have hLammass : lam.real univ = A := by
    change (Measure.conv μ ν).real univ = A
    rw [l6a_conv_mass_prob μ ν, hνmass]
  have hLamball (z : Rd d) (s : ℝ) (hs : 0 < s) :
      lam.real (closedBall z s) ≤ (2 ^ d : ℝ) * A * s := by
    change (Measure.conv μ ν).real (closedBall z s) ≤ _
    have h := l6a_conv_smallBall μ ν (by positivity : 0 ≤ (2 ^ d : ℝ))
      (fun z s hs => by
        exact unitSphereProb_smallBall hd z s hs) z s hs
    rwa [hνmass] at h
  obtain ⟨hLammoment, hLammoment_le⟩ :=
    l6a_conv_logMoment μ ν hμmoment hνmoment
  refine ⟨inferInstance, hLammass, hLamball, hLammoment, ?_⟩
  change (∫ z : Rd d, Real.log (2 + ‖z‖) ∂(Measure.conv μ ν)) ≤ _
  calc
    _ ≤ ν.real univ * (∫ x : Rd d, Real.log (2 + ‖x‖) ∂μ) +
      μ.real univ * (∫ x : Rd d, Real.log (2 + ‖x‖) ∂ν) := hLammoment_le
    _ ≤ A * Real.log 3 + B := by
      rw [hνmass, probReal_univ, one_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hμmoment_le (by
          dsimp [A]
          exact integral_nonneg fun _ => abs_nonneg _)) hνmoment_le

end HigherDimLQGMetric
