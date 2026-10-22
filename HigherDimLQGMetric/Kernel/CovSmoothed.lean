import HigherDimLQGMetric.Kernel.CovKernelMoment
import HigherDimLQGMetric.LGF.Density

/-!
# Basic estimates for finite-measure convolutions
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem convKernelEps_bounded (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Rd d, |convKernelEps κ ε x| ≤ B := by
  obtain ⟨C, hC⟩ := convKernel_decay hd hκ
  refine ⟨ε ^ (-(d : ℝ)) * max C 0, mul_nonneg (Real.rpow_nonneg hε.le _) (le_max_right _ _),
    fun x => ?_⟩
  have hpow : (1 + ‖ε⁻¹ • x‖) ^ (-((d : ℝ) + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [norm_nonneg (ε⁻¹ • x)]) (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith)
  have hC' : |convKernel κ (ε⁻¹ • x)| ≤ max C 0 := by
    calc
      |convKernel κ (ε⁻¹ • x)| ≤ C * (1 + ‖ε⁻¹ • x‖) ^ (-((d : ℝ) + 1)) := hC _
      _ ≤ max C 0 * (1 + ‖ε⁻¹ • x‖) ^ (-((d : ℝ) + 1)) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C 0 := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hpow (le_max_right C 0)
  rw [convKernelEps, abs_mul, abs_of_nonneg (Real.rpow_nonneg hε.le _)]
  exact mul_le_mul_of_nonneg_left hC' (Real.rpow_nonneg hε.le _)

theorem measurable_measConv (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ε : ℝ)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] :
    Measurable (measConv κ ε μ) := by
  have hc : Continuous (convKernelEps κ ε) :=
    continuous_const.mul
      ((convKernel_contDiff (by omega) hκ).continuous.comp
        (continuous_const_smul _))
  have hm : Measurable (fun p : Rd d × Rd d =>
      convKernelEps κ ε (p.1 - p.2)) :=
    hc.measurable.comp (measurable_fst.sub measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem abs_measConv_le (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Rd d, |measConv κ ε μ x| ≤ B := by
  obtain ⟨B, hB, hbound⟩ := convKernelEps_bounded hd hκ hε
  refine ⟨B * μ.real Set.univ, mul_nonneg hB measureReal_nonneg, fun x => ?_⟩
  have h := norm_integral_le_of_norm_le_const
    (C := B) (μ := μ) (f := fun z : Rd d => convKernelEps κ ε (x - z))
    (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hbound (x - z))
  simpa only [measConv, Real.norm_eq_abs] using h

theorem integrable_prod_convKernelEps (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] :
    Integrable (fun p : Rd d × Rd d =>
      convKernelEps κ ε (p.1 - p.2)) (volume.prod μ) := by
  let F : Rd d × Rd d → ℝ := fun p => convKernelEps κ ε (p.1 - p.2)
  have hc : Continuous F := by
    dsimp [F]
    exact (continuous_const.mul
      ((convKernel_contDiff (by omega) hκ).continuous.comp
        (continuous_const_smul _))).comp (continuous_fst.sub continuous_snd)
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun z => by
      change Integrable (fun x => convKernelEps κ ε (x - z))
      exact (integrable_convKernelEps hd hκ hε).comp_sub_right z
  · have he : (fun z : Rd d => ∫ x, ‖F (x, z)‖) =
        fun _ => ∫ x : Rd d, |convKernelEps κ ε x| := by
      funext z
      dsimp [F]
      exact integral_sub_right_eq_self (fun x : Rd d => |convKernelEps κ ε x|) z
    rw [he]
    exact integrable_const _

theorem integrable_measConv (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] :
    Integrable (measConv κ ε μ) := by
  have h := (integrable_prod_convKernelEps hd hκ hε μ).integral_prod_left
  change Integrable (measConv κ ε μ) at h
  exact h

theorem integral_measConv_eq_mass (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] :
    ∫ x : Rd d, measConv κ ε μ x = μ.real Set.univ := by
  let F : Rd d × Rd d → ℝ := fun p => convKernelEps κ ε (p.1 - p.2)
  have hF : Integrable F (volume.prod μ) :=
    integrable_prod_convKernelEps hd hκ hε μ
  change (∫ x : Rd d, ∫ z : Rd d, F (x, z) ∂μ) = μ.real Set.univ
  rw [integral_integral_swap hF]
  have he (z : Rd d) : (∫ x : Rd d, F (x, z)) = 1 := by
    change (∫ x : Rd d, convKernelEps κ ε (x - z)) = 1
    rw [integral_sub_right_eq_self (convKernelEps κ ε) z,
      integral_convKernelEps_eq_one hd hκ hε]
  simp_rw [he]
  simp

private theorem logWeight_le_add (x z : Rd d) :
    Real.log (2 + ‖x‖) ≤
      Real.log (2 + ‖x - z‖) + Real.log (2 + ‖z‖) := by
  have hx : 0 < 2 + ‖x‖ := by positivity
  have hu : 0 < 2 + ‖x - z‖ := by positivity
  have hz : 0 < 2 + ‖z‖ := by positivity
  have hnorm : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
    have h := norm_add_le (x - z) z
    rwa [sub_add_cancel] at h
  have hp : 2 + ‖x‖ ≤ (2 + ‖x - z‖) * (2 + ‖z‖) := by
    nlinarith [norm_nonneg (x - z), norm_nonneg z]
  rw [← Real.log_mul hu.ne' hz.ne']
  exact Real.log_le_log hx hp

private theorem logWeight_nonneg (x : Rd d) :
    0 ≤ Real.log (2 + ‖x‖) :=
  Real.log_nonneg (by nlinarith [norm_nonneg x])

theorem integrable_logWeight_of_ae_bounded
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] {D : ℝ}
    (hD : ∀ᵐ z ∂μ, ‖z‖ ≤ D) :
    Integrable (fun z : Rd d => Real.log (2 + ‖z‖)) μ := by
  have hC : 0 ≤ Real.log (2 + max D 0) :=
    Real.log_nonneg (by nlinarith [le_max_right D 0])
  apply Integrable.of_bound
    ((measurable_const.add measurable_norm).log.aestronglyMeasurable)
    (Real.log (2 + max D 0))
  filter_upwards [hD] with z hz
  change |Real.log (2 + ‖z‖)| ≤ Real.log (2 + max D 0)
  rw [abs_of_nonneg (logWeight_nonneg z)]
  exact Real.log_le_log (by positivity)
    (by nlinarith [hz, le_max_left D 0])

theorem integrable_logMoment_measConv (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (hmoment : Integrable (fun z : Rd d => Real.log (2 + ‖z‖)) μ) :
    Integrable (fun x : Rd d => Real.log (2 + ‖x‖) * measConv κ ε μ x) := by
  let w : Rd d → ℝ := fun x => Real.log (2 + ‖x‖)
  let K : Rd d → ℝ := convKernelEps κ ε
  let G : Rd d × Rd d → ℝ := fun p => (w (p.1 - p.2) + w p.2) * |K (p.1 - p.2)|
  have hK : Integrable K := integrable_convKernelEps hd hκ hε
  have hwK : Integrable (fun x => w x * K x) :=
    integrable_logMoment_convKernelEps hd hκ hε
  have hw : Continuous w := by
    dsimp [w]
    apply Continuous.log
    · fun_prop
    · intro x; positivity
  have hcK : Continuous K :=
    continuous_const.mul
      ((convKernel_contDiff (by omega) hκ).continuous.comp
        (continuous_const_smul _))
  have hG : Integrable G (volume.prod μ) := by
    have hc : Continuous G := by
      exact (((hw.comp (continuous_fst.sub continuous_snd)).add
        (hw.comp continuous_snd)).mul
          (continuous_abs.comp (hcK.comp (continuous_fst.sub continuous_snd))))
    apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun z => by
        have h1 := hwK.norm.comp_sub_right z
        have h2 := (hK.norm.comp_sub_right z).const_mul (w z)
        have heq : (fun x : Rd d => G (x, z)) =
            fun x => ‖w (x - z) * K (x - z)‖ + w z * ‖K (x - z)‖ := by
          funext x
          dsimp [G]
          rw [abs_mul, abs_of_nonneg (logWeight_nonneg (x - z))]
          ring
        rw [heq]
        exact h1.add h2
    · have he (z : Rd d) :
          (∫ x : Rd d, ‖G (x, z)‖) =
            (∫ x : Rd d, |w x * K x|) +
              w z * (∫ x : Rd d, |K x|) := by
        have h1 := hwK.norm.comp_sub_right z
        have h2 := (hK.norm.comp_sub_right z).const_mul (w z)
        have hcongr : (fun x : Rd d => ‖G (x, z)‖) =
            fun x => |w (x - z) * K (x - z)| + w z * |K (x - z)| := by
          funext x
          dsimp [G]
          rw [abs_mul,
            abs_of_nonneg (add_nonneg (logWeight_nonneg _) (logWeight_nonneg _)),
            abs_mul, abs_of_nonneg (logWeight_nonneg _)]
          simp only [abs_abs]
          ring
        have h1' : Integrable (fun x : Rd d => |w (x - z) * K (x - z)|) := by
          simpa only [Real.norm_eq_abs] using h1
        have h2' : Integrable (fun x : Rd d => w z * |K (x - z)|) := by
          simpa only [Real.norm_eq_abs] using h2
        rw [hcongr, integral_add h1' h2', integral_const_mul,
          integral_sub_right_eq_self (fun x : Rd d => |w x * K x|) z,
          integral_sub_right_eq_self (fun x : Rd d => |K x|) z]
      simp_rw [he]
      exact (integrable_const _).add (hmoment.mul_const _)
  let H : Rd d × Rd d → ℝ := fun p => w p.1 * K (p.1 - p.2)
  have hH : Integrable H (volume.prod μ) := by
    apply hG.mono'
    · have hc : Continuous H := by
        exact (hw.comp continuous_fst).mul
          (hcK.comp (continuous_fst.sub continuous_snd))
      exact hc.aestronglyMeasurable
    · refine ae_of_all _ fun p => ?_
      have hw := logWeight_le_add p.1 p.2
      have hn : 0 ≤ w (p.1 - p.2) + w p.2 :=
        add_nonneg (logWeight_nonneg _) (logWeight_nonneg _)
      dsimp [H, G]
      rw [abs_mul, abs_of_nonneg (logWeight_nonneg _)]
      exact mul_le_mul_of_nonneg_right hw (abs_nonneg _)
  have hi := hH.integral_prod_left
  convert hi using 1
  ext x
  dsimp [H, w, K, measConv]
  rw [integral_const_mul]

end HigherDimLQGMetric
