import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Signed.Kernel
import HigherDimLQGMetric.Kernel.ConvKernelInversion
import HigherDimLQGMetric.Kernel.ConvKernelGlobalIntegrable
import HigherDimLQGMetric.Kernel.ConvKernelDirectional
import HigherDimLQGMetric.Kernel.ConvKernelFourierDecay
import HigherDimLQGMetric.Kernel.ConvKernelMain
import HigherDimLQGMetric.Kernel.CovKernelEps
import HigherDimLQGMetric.Kernel.CovKernelMoment

/-!
# Sign-free copies: the kernel `K = convKernel κ`: inversion, decay, integrability, `l1c_convKernel`

Packet G1 (ruling L7; planning audit `planning/audits/MA3-inputs.md` §4.1 and §4.3 items 1–2). The declarations of
`HigherDimLQGMetric.Kernel.ConvKernelInversion`, `HigherDimLQGMetric.Kernel.ConvKernelGlobalIntegrable`,
`HigherDimLQGMetric.Kernel.ConvKernelDirectional`, `HigherDimLQGMetric.Kernel.ConvKernelFourierDecay`,
`HigherDimLQGMetric.Kernel.ConvKernelMain`, `HigherDimLQGMetric.Kernel.CovKernelEps`,
`HigherDimLQGMetric.Kernel.CovKernelMoment`
whose statements mention the kernel predicate, copied with hypothesis `HigherDimLFPPAS.IsAdmissibleSeed κ` (the
paper's seeds: no sign condition) in place of `HigherDimLFPP.IsLFPPKernel κ`. Each copy `<name>_seed` has the
statement of `HigherDimLQGMetric.<name>` except for the kernel hypothesis (kernel-dependent definitions it mentions
are replaced by their copies); its proof is the host proof, with calls to copied declarations redirected to the
copies and everything else reused directly. Host-private helpers called by the copied proofs are copied as private
`<name>_seed`.
No proof uses nonnegativity of the seed: `IsAdmissibleSeed` has no such field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Signed

open HigherDimLQGMetric

section ConvKernelInversion
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelInversion`. -/

open MeasureTheory
open scoped FourierTransform
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Fourier inversion for the kernel, given spatial integrability.
Sign-free copy of `HigherDimLQGMetric.convKernel_fourier_eq`. -/
theorem convKernel_fourier_eq_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hK : Integrable (convKernel κ)) :
    𝓕 (fun x : Rd d => (convKernel κ x : ℂ)) =
      fun ζ => (kernelSymbol κ ζ : ℂ) := by
  let o : Rd d → ℂ := fun ζ => (kernelSymbol κ ζ : ℂ)
  have hcont : Continuous o :=
    Complex.continuous_ofReal.comp (kernelSymbol_continuous_seed hd hκ)
  have ho : Integrable o := by
    apply (integrable_norm_iff hcont.aestronglyMeasurable).mp
    simpa [o] using integrable_kernelSymbol_complex_moment_seed hd hκ 0
  have hFour : Integrable (𝓕 o) := by
    have hkc : Integrable (fun x : Rd d => (convKernel κ x : ℂ)) := hK.ofReal
    have hneg := hkc.comp_neg
    convert hneg using 1
    funext x
    have h := Real.fourierInv_eq_fourier_neg o (-x)
    simp only [neg_neg] at h
    rw [← h]
    exact (convKernel_complex_eq_fourierInv (κ := κ) (-x)).symm
  have h := hcont.fourier_fourierInv_eq ho hFour
  have heq : (fun x : Rd d => (convKernel κ x : ℂ)) = 𝓕⁻ o := by
    funext x
    exact convKernel_complex_eq_fourierInv x
  rw [heq]
  exact h

/-- The integral of the kernel is one, given spatial integrability.
Sign-free copy of `HigherDimLQGMetric.convKernel_integral_eq_one`. -/
theorem convKernel_integral_eq_one_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hK : Integrable (convKernel κ)) :
    ∫ x : Rd d, convKernel κ x = 1 := by
  have h0 := congrFun (convKernel_fourier_eq_seed hd hκ hK) (0 : Rd d)
  have hm : (∫ x : Rd d, (convKernel κ x : ℂ)) = 1 := by
    simpa [Real.fourier_eq, kernelSymbol_zero_seed hd hκ] using h0
  rw [integral_complex_ofReal] at hm
  exact_mod_cast hm

end ConvKernelInversion

section ConvKernelGlobalIntegrable
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelGlobalIntegrable`. -/

open MeasureTheory Set
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Copy of the host-private helper `HigherDimLQGMetric.integrableOn_inv_norm_pow_outside` (no kernel hypothesis). -/
private theorem integrableOn_inv_norm_pow_outside_seed (N : ℕ) (hN : d < N) :
    IntegrableOn (fun ζ : Rd d => ‖ζ‖ ^ (-(N : ℝ)))
      {ζ : Rd d | 1 ≤ ‖ζ‖} := by
  have hint : Integrable (fun ζ : Rd d => (1 + ‖ζ‖) ^ (-(N : ℝ))) := by
    apply integrable_one_add_norm (μ := volume)
    simpa only [finrank_euclideanSpace_fin] using (by exact_mod_cast hN : (d : ℝ) < N)
  apply ((hint.const_mul (2 ^ N : ℝ)).integrableOn).mono'
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm :
      MeasurableSet {ζ : Rd d | 1 ≤ ‖ζ‖})]
      with ζ hζ
    have hr : 0 < ‖ζ‖ := lt_of_lt_of_le (by norm_num) hζ
    have hs : 0 < 1 + ‖ζ‖ := by positivity
    have hpow : (1 + ‖ζ‖) ^ N ≤ (2 : ℝ) ^ N * ‖ζ‖ ^ N := by
      calc
        _ ≤ (2 * ‖ζ‖) ^ N := by gcongr; linarith
        _ = _ := by rw [mul_pow]
    have hbound : ‖ζ‖ ^ (-(N : ℝ)) ≤
        (2 : ℝ) ^ N * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg hr.le, Real.rpow_natCast,
        Real.rpow_neg hs.le, Real.rpow_natCast]
      have hfrac : (1 : ℝ) / ‖ζ‖ ^ N ≤
          (2 : ℝ) ^ N / (1 + ‖ζ‖) ^ N :=
        (div_le_div_iff₀ (pow_pos hr N) (pow_pos hs N)).mpr
          (by simpa only [one_mul] using hpow)
      simpa only [one_div, div_eq_mul_inv, one_mul] using hfrac
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr.le _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ N *
        (1 + ‖ζ‖) ^ (-(N : ℝ)))] using hbound

/-- Sign-free copy of `HigherDimLQGMetric.kernelSymbol_deriv_aestronglyMeasurable`. -/
private theorem kernelSymbol_deriv_aestronglyMeasurable_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) :
    AEStronglyMeasurable (iteratedFDeriv ℝ n (kernelSymbol κ)) volume := by
  let : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using hd)
  have hcont : ContinuousOn (iteratedFDeriv ℝ n (kernelSymbol κ))
      ({0}ᶜ : Set (Rd d)) :=
    ContinuousOn.continuousOn_iteratedFDeriv
      (kernelSymbol_contDiffOn_seed hd hκ) (isClosed_singleton.isOpen_compl) (by simp)
  have hh := hcont.aestronglyMeasurable (μ := volume)
    (isClosed_singleton.isOpen_compl.measurableSet)
  have hfull : volume.restrict ({0}ᶜ : Set (Rd d)) = volume :=
    Measure.restrict_eq_self_of_ae_mem (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (Measure.ae_ne volume (0 : Rd d)))
  rwa [hfull] at hh

/-- Sign-free copy of `HigherDimLQGMetric.kernelSymbol_deriv_continuousOn`. -/
private theorem kernelSymbol_deriv_continuousOn_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ n (kernelSymbol κ))
      ({0}ᶜ : Set (Rd d)) :=
  ContinuousOn.continuousOn_iteratedFDeriv
    (kernelSymbol_contDiffOn_seed hd hκ) (isClosed_singleton.isOpen_compl) (by simp)

/-- Sign-free copy of `HigherDimLQGMetric.integrableOn_symbol_deriv_moment_near`. -/
private theorem integrableOn_symbol_deriv_moment_near_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n k : ℕ) (hn : 0 < n)
    (hnd : n < 2 * d) :
    ∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn
      (fun ζ : Rd d => ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)
      (Metric.ball (0 : Rd d) ρ) := by
  obtain ⟨ρ, hρ, hnear⟩ :=
    integrableOn_kernelSymbol_iteratedFDeriv_near_zero_seed hd hκ n hn hnd
  refine ⟨ρ, hρ, ?_⟩
  apply ((hnear.norm).const_mul (ρ ^ k)).mono'
  · exact ((measurable_norm.pow_const k).aestronglyMeasurable).mul
      (kernelSymbol_deriv_aestronglyMeasurable_seed hd hκ n).norm |>.restrict
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with ζ hζ
    have hr : ‖ζ‖ ≤ ρ := by
      have hh : ‖ζ‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hζ
      exact hh.le
    have hpow := pow_le_pow_left₀ (norm_nonneg ζ) hr k
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)] using
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)

/-- Sign-free copy of `HigherDimLQGMetric.integrableOn_symbol_deriv_moment_outside`. -/
private theorem integrableOn_symbol_deriv_moment_outside_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n k : ℕ) :
    IntegrableOn
      (fun ζ : Rd d => ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)
      {ζ : Rd d | 1 ≤ ‖ζ‖} := by
  let N := d + 1
  obtain ⟨C, hC⟩ := kernelSymbol_iteratedFDeriv_decay_seed hd hκ n (k + N)
  have hsource : IntegrableOn (fun ζ : Rd d => C * ‖ζ‖ ^ (-(N : ℝ)))
      {ζ : Rd d | 1 ≤ ‖ζ‖} :=
    (integrableOn_inv_norm_pow_outside_seed N (by dsimp [N]; omega)).const_mul C
  apply hsource.mono'
  · exact (((measurable_norm.pow_const k).aestronglyMeasurable).mul
      (kernelSymbol_deriv_aestronglyMeasurable_seed hd hκ n).norm).restrict
  · filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm :
        MeasurableSet {ζ : Rd d | 1 ≤ ‖ζ‖})] with ζ hζ
    have hr : 0 < ‖ζ‖ := lt_of_lt_of_le (by norm_num) hζ
    have hpow : ‖ζ‖ ^ N *
        (‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖) ≤ C := by
      simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc] using hC ζ hζ
    have hbound : ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤
        C * ‖ζ‖ ^ (-(N : ℝ)) := by
      have hh : ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤
          C / ‖ζ‖ ^ N := (le_div_iff₀ (pow_pos hr N)).mpr (by
            simpa only [mul_comm] using hpow)
      simpa only [Real.rpow_neg hr.le, Real.rpow_natCast, div_eq_mul_inv] using hh
    have hs : 0 ≤ C * ‖ζ‖ ^ (-(N : ℝ)) := le_trans (by positivity) hbound
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ‖ζ‖ ^ k *
        ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖), abs_of_nonneg hs] using hbound

/-- Sign-free copy of `HigherDimLQGMetric.integrableOn_symbol_deriv_moment_annulus`. -/
private theorem integrableOn_symbol_deriv_moment_annulus_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n k : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn
      (fun ζ : Rd d => ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)
      (Metric.closedBall (0 : Rd d) 1 \ Metric.ball 0 ρ) := by
  have hsubset : Metric.closedBall (0 : Rd d) 1 \ Metric.ball 0 ρ ⊆
      ({0}ᶜ : Set (Rd d)) := by
    intro ζ hζ
    change ζ ≠ 0
    intro he
    subst ζ
    exact hζ.2 (Metric.mem_ball_self hρ)
  have hcont : ContinuousOn
      (fun ζ : Rd d => ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)
      (Metric.closedBall (0 : Rd d) 1 \ Metric.ball 0 ρ) :=
    ((continuous_norm.pow k).continuousOn.mul
      (kernelSymbol_deriv_continuousOn_seed hd hκ n).norm).mono hsubset
  exact hcont.integrableOn_compact ((isCompact_closedBall _ _).diff Metric.isOpen_ball)

/-- The `k`-th moment of the norm of each symbol derivative of order `n < 2d` is integrable.
Sign-free copy of `HigherDimLQGMetric.integrable_kernelSymbol_iteratedFDeriv_moment`. -/
theorem integrable_kernelSymbol_iteratedFDeriv_moment_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n k : ℕ) (hnd : n < 2 * d) :
    Integrable (fun ζ : Rd d =>
      ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖) := by
  by_cases hn : n = 0
  · subst n
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      integrable_kernelSymbol_moment_seed hd hκ k
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨ρ, hρ, hnear⟩ :=
    integrableOn_symbol_deriv_moment_near_seed hd hκ n k hn hnd
  have hann := integrableOn_symbol_deriv_moment_annulus_seed hd hκ n k hρ
  have hout : IntegrableOn
      (fun ζ : Rd d => ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)
      (Metric.closedBall (0 : Rd d) 1)ᶜ :=
    (integrableOn_symbol_deriv_moment_outside_seed hd hκ n k).mono_set (by
      intro ζ hζ
      have hnot : ¬ ‖ζ‖ ≤ 1 := by
        simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] using hζ
      exact le_of_lt (lt_of_not_ge hnot))
  have hunion := (hnear.union hann).union hout
  have hcover : Set.univ ⊆
      (Metric.ball (0 : Rd d) ρ ∪
        (Metric.closedBall (0 : Rd d) 1 \ Metric.ball 0 ρ)) ∪
        (Metric.closedBall (0 : Rd d) 1)ᶜ := by
    intro ζ _
    by_cases hb : ζ ∈ Metric.ball (0 : Rd d) ρ
    · exact Or.inl (Or.inl hb)
    by_cases hc : ζ ∈ Metric.closedBall (0 : Rd d) 1
    · exact Or.inl (Or.inr ⟨hc, hb⟩)
    · exact Or.inr hc
  simpa only [integrableOn_univ] using hunion.mono_set hcover

end ConvKernelGlobalIntegrable

section ConvKernelDirectional
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelDirectional`. -/

open MeasureTheory Set
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.directionalSymbol_hasLineDerivAt`. -/
theorem directionalSymbol_hasLineDerivAt_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (v : Rd d) (n : ℕ)
    {ζ : Rd d} (hζ : ζ ≠ 0) :
    HasLineDerivAt ℝ (directionalSymbol κ v n)
      (directionalSymbol κ v (n + 1) ζ) ζ v := by
  have hs : IsOpen ({0}ᶜ : Set (Rd d)) := isClosed_singleton.isOpen_compl
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (kernelSymbol κ) ζ :=
    (kernelSymbol_contDiffOn_seed hd hκ).contDiffAt (hs.mem_nhds hζ)
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n (kernelSymbol κ)) ζ :=
    hcd.differentiableAt_iteratedFDeriv (by
      exact_mod_cast (show (n : ℕ∞) < ⊤ from by simp))
  have hreal : HasFDerivAt
      (fun x : Rd d => (iteratedFDeriv ℝ n (kernelSymbol κ) x) (fun _ => v))
      (fderiv ℝ (fun x : Rd d => (iteratedFDeriv ℝ n (kernelSymbol κ) x)
        (fun _ => v)) ζ) ζ :=
    (hdiff.continuousMultilinear_apply_const (fun _ => v)).hasFDerivAt
  have heq : (fderiv ℝ (fun x : Rd d =>
        (iteratedFDeriv ℝ n (kernelSymbol κ) x) (fun _ => v)) ζ) v =
      (iteratedFDeriv ℝ (n + 1) (kernelSymbol κ) ζ) (fun _ => v) := by
    rw [fderiv_continuousMultilinear_apply_const_apply hdiff]
    rw [iteratedFDeriv_succ_apply_left]
    rfl
  have hc : HasFDerivAt (directionalSymbol κ v n)
      (Complex.ofRealCLM.comp
        (fderiv ℝ (fun x : Rd d =>
          (iteratedFDeriv ℝ n (kernelSymbol κ) x) (fun _ => v)) ζ)) ζ := by
    exact Complex.ofRealCLM.hasFDerivAt.comp ζ hreal
  have heval : (Complex.ofRealCLM.comp
      (fderiv ℝ (fun x : Rd d =>
        (iteratedFDeriv ℝ n (kernelSymbol κ) x) (fun _ => v)) ζ)) v =
      directionalSymbol κ v (n + 1) ζ := by
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, heq,
      directionalSymbol]
  rw [← heval]
  exact hc.hasLineDerivAt v

/-- Sign-free copy of `HigherDimLQGMetric.directionalSymbol_aestronglyMeasurable`. -/
theorem directionalSymbol_aestronglyMeasurable_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (v : Rd d) (n : ℕ) :
    AEStronglyMeasurable (directionalSymbol κ v n) volume := by
  let : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    simpa only [finrank_euclideanSpace_fin] using hd)
  have hderiv : ContinuousOn (iteratedFDeriv ℝ n (kernelSymbol κ))
      ({0}ᶜ : Set (Rd d)) :=
    ContinuousOn.continuousOn_iteratedFDeriv
      (kernelSymbol_contDiffOn_seed hd hκ) (isClosed_singleton.isOpen_compl) (by simp)
  have hcont : ContinuousOn (directionalSymbol κ v n) ({0}ᶜ : Set (Rd d)) := by
    have heval : Continuous
        (fun p : (Rd d) [×n]→L[ℝ] ℝ => p (fun _ => v)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Rd d) ℝ (fun _ => v)).continuous
    exact Complex.continuous_ofReal.comp_continuousOn
      (heval.comp_continuousOn hderiv)
  have hh := hcont.aestronglyMeasurable (μ := volume)
    (isClosed_singleton.isOpen_compl.measurableSet)
  have hfull : volume.restrict ({0}ᶜ : Set (Rd d)) = volume :=
    Measure.restrict_eq_self_of_ae_mem (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (Measure.ae_ne volume (0 : Rd d)))
  rwa [hfull] at hh

/-- Sign-free copy of `HigherDimLQGMetric.integrable_directionalSymbol`. -/
theorem integrable_directionalSymbol_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (v : Rd d) (n : ℕ) (hnd : n < 2 * d) :
    Integrable (directionalSymbol κ v n) := by
  have hsource : Integrable (fun ζ : Rd d =>
      ‖v‖ ^ n * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖) := by
    simpa only [pow_zero, one_mul] using
      (integrable_kernelSymbol_iteratedFDeriv_moment_seed hd hκ n 0 hnd).const_mul (‖v‖ ^ n)
  apply hsource.mono' (directionalSymbol_aestronglyMeasurable_seed hd hκ v n)
  filter_upwards with ζ
  have hbound := ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ n (kernelSymbol κ) ζ) (fun _ : Fin n => v)
  have hprod : ∏ _ : Fin n, ‖v‖ = ‖v‖ ^ n := by simp
  simpa only [directionalSymbol, Complex.norm_real, ← Real.norm_eq_abs,
    hprod, mul_comm] using hbound

end ConvKernelDirectional

section ConvKernelFourierDecay
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelFourierDecay`. -/

open Real Complex MeasureTheory Set
open scoped FourierTransform Real
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Copy of the host-private helper `HigherDimLQGMetric.fourierPhase_norm` (no kernel hypothesis). -/
private theorem fourierPhase_norm_seed (x ζ : Rd d) : ‖fourierPhase x ζ‖ = 1 := by
  simp [fourierPhase]

/-- Copy of the host-private helper `HigherDimLQGMetric.fourierPhase_hasLineDerivAt` (no kernel hypothesis). -/
private theorem fourierPhase_hasLineDerivAt_seed (x v ζ : Rd d) :
    HasLineDerivAt ℝ (fourierPhase x)
      ((-2 * π * Complex.I * innerSL ℝ v x) * fourierPhase x ζ) ζ v := by
  have hd := Real.differentiable_fourierChar_neg_bilinear_left (innerSL ℝ) x ζ
  have h := hd.hasFDerivAt.hasLineDerivAt v
  have heq : fderiv ℝ (fourierPhase x) ζ v =
      (-2 * π * Complex.I * innerSL ℝ v x) * fourierPhase x ζ := by
    change (fderiv ℝ (fun z : Rd d => (𝐞 (-(innerSL ℝ z x)) : ℂ)) ζ) v =
      (-2 * π * Complex.I * innerSL ℝ v x) *
        (𝐞 (-(innerSL ℝ ζ x)) : ℂ)
    simpa only using
      Real.fderiv_fourierChar_neg_bilinear_left_apply (innerSL ℝ) ζ v x
  rw [← heq]
  exact h

/-- Sign-free copy of `HigherDimLQGMetric.integrable_fourierPhase_mul_directional`. -/
private theorem integrable_fourierPhase_mul_directional_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (v x : Rd d) (n : ℕ)
    (hnd : n < 2 * d) :
    Integrable (fun ζ : Rd d => fourierPhase x ζ * directionalSymbol κ v n ζ) := by
  have hphase : AEStronglyMeasurable (fourierPhase x) volume := by
    apply Measurable.aestronglyMeasurable
    unfold fourierPhase
    fun_prop
  have hbound : ∀ᵐ ζ : Rd d ∂volume, ‖fourierPhase x ζ‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall (fun ζ => le_of_eq (fourierPhase_norm_seed x ζ))
  have h := (integrable_directionalSymbol_seed hd hκ v n hnd).mul_bdd hphase hbound
  convert h using 1
  ext ζ
  exact mul_comm _ _

/-- Sign-free copy of `HigherDimLQGMetric.directional_fourier_step`. -/
theorem directional_fourier_step_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (v x : Rd d) (hv : v ≠ 0)
    (n : ℕ) (hn : n + 1 < 2 * d) :
    (∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v (n+1) ζ) =
      (2 * π * Complex.I * innerSL ℝ v x) *
        (∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v n ζ) := by
  let c : ℂ := -2 * π * Complex.I * innerSL ℝ v x
  have h0 : Integrable (fun ζ : Rd d =>
      fourierPhase x ζ * directionalSymbol κ v n ζ) :=
    integrable_fourierPhase_mul_directional_seed (by omega) hκ v x n (by omega)
  have h1 : Integrable (fun ζ : Rd d =>
      fourierPhase x ζ * directionalSymbol κ v (n+1) ζ) :=
    integrable_fourierPhase_mul_directional_seed (by omega) hκ v x (n+1) hn
  have hp : Integrable (fun ζ : Rd d =>
      (c * fourierPhase x ζ) * directionalSymbol κ v n ζ) := by
    convert h0.const_mul c using 1
    ext ζ
    ring
  have hdim : 2 ≤ Module.finrank ℝ (Rd d) := by
    simpa only [finrank_euclideanSpace_fin] using hd
  have h := integral_bilinear_line_except_zero
    (B := ContinuousLinearMap.mul ℝ ℂ)
    (f := fourierPhase x)
    (f' := fun ζ => c * fourierPhase x ζ)
    (g := directionalSymbol κ v n)
    (g' := directionalSymbol κ v (n+1))
    (v := v) (μ := volume)
    hdim hp h1 h0 hv
    (fun ζ => by simpa only [c] using fourierPhase_hasLineDerivAt_seed x v ζ)
    (fun ζ hζ => directionalSymbol_hasLineDerivAt_seed (by omega) hκ v n hζ)
  dsimp at h
  simp_rw [mul_assoc] at h
  rw [integral_const_mul] at h
  convert h using 1
  ring

/-- Sign-free copy of `HigherDimLQGMetric.directional_fourier_pow`. -/
private theorem directional_fourier_pow_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (v x : Rd d) (hv : v ≠ 0)
    (n : ℕ) (hn : n < 2 * d) :
    (∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v n ζ) =
      (2 * π * Complex.I * innerSL ℝ v x) ^ n *
        (∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v 0 ζ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [directional_fourier_step_seed hd hκ v x hv n hn,
      ih (by omega), pow_succ]
    ring

/-- Copy of the host-private helper `HigherDimLQGMetric.directional_fourier_zero_eq` (no kernel hypothesis). -/
private theorem directional_fourier_zero_eq_seed (v x : Rd d) :
    (∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v 0 ζ) =
      𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x := by
  rw [Real.fourier_eq]
  congr 1

/-- Sign-free copy of `HigherDimLQGMetric.norm_directional_fourier_integral_le`. -/
private theorem norm_directional_fourier_integral_le_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (v x : Rd d)
    (hv : ‖v‖ = 1) (n : ℕ) (hn : n < 2 * d) :
    ‖∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v n ζ‖ ≤
      ∫ ζ : Rd d, ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ := by
  have hint : Integrable (fun ζ : Rd d =>
      ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖) := by
    simpa only [pow_zero, one_mul] using
      integrable_kernelSymbol_iteratedFDeriv_moment_seed (by omega) hκ n 0 hn
  have hfn : Integrable (fun ζ : Rd d =>
      fourierPhase x ζ * directionalSymbol κ v n ζ) :=
    integrable_fourierPhase_mul_directional_seed (by omega) hκ v x n hn
  calc
    _ ≤ ∫ ζ : Rd d, ‖fourierPhase x ζ * directionalSymbol κ v n ζ‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ζ : Rd d, ‖directionalSymbol κ v n ζ‖ := by
      congr 1
      funext ζ
      rw [norm_mul, fourierPhase_norm_seed, one_mul]
    _ ≤ ∫ ζ : Rd d, ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ := by
      apply integral_mono (integrable_directionalSymbol_seed (by omega) hκ v n hn).norm hint
      intro ζ
      have hb := ContinuousMultilinearMap.le_opNorm
        (iteratedFDeriv ℝ n (kernelSymbol κ) ζ) (fun _ : Fin n => v)
      simpa only [directionalSymbol, Complex.norm_real, ← Real.norm_eq_abs,
        Finset.prod_const, Fintype.card_fin, hv, one_pow, mul_one] using hb

/-- Copy of the host-private helper `HigherDimLQGMetric.unitDirection_norm` (no kernel hypothesis). -/
private theorem unitDirection_norm_seed (x : Rd d) (hx : x ≠ 0) :
    ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp [norm_smul, hr]

/-- Copy of the host-private helper `HigherDimLQGMetric.inner_unitDirection` (no kernel hypothesis). -/
private theorem inner_unitDirection_seed (x : Rd d) (hx : x ≠ 0) :
    innerSL ℝ ((‖x‖⁻¹ : ℝ) • x) x = ‖x‖ := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [innerSL_apply_apply, real_inner_smul_left,
    real_inner_self_eq_norm_sq, sq]
  field_simp

/-- Sign-free copy of `HigherDimLQGMetric.fourier_symbol_pow_bound`. -/
private theorem fourier_symbol_pow_bound_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (v x : Rd d)
    (hv : ‖v‖ = 1) (n : ℕ) (hn : n < 2 * d) :
    ‖(2 * π * Complex.I * innerSL ℝ v x) ^ n‖ *
      ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
      ∫ ζ : Rd d, ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ := by
  have hv0 : v ≠ 0 := by intro he; simp [he] at hv
  have hpow := directional_fourier_pow_seed hd hκ v x hv0 n hn
  rw [directional_fourier_zero_eq_seed] at hpow
  have hnorm := norm_directional_fourier_integral_le_seed hd hκ v x hv n hn
  rw [hpow, norm_mul] at hnorm
  exact hnorm

/-- Sign-free copy of `HigherDimLQGMetric.fourier_symbol_spatial_pow_bound`. -/
theorem fourier_symbol_spatial_pow_bound_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) (hn : n < 2 * d) :
    ∀ x : Rd d, x ≠ 0 →
      ‖x‖ ^ n * ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
        ∫ ζ : Rd d, ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ := by
  intro x hx
  let v : Rd d := (‖x‖⁻¹ : ℝ) • x
  have hv : ‖v‖ = 1 := unitDirection_norm_seed x hx
  have hi : innerSL ℝ v x = ‖x‖ := inner_unitDirection_seed x hx
  have h := fourier_symbol_pow_bound_seed hd hκ v x hv n hn
  rw [hi, norm_pow] at h
  have hcoef : ‖(2 * π * Complex.I * (‖x‖ : ℂ))‖ = 2 * π * ‖x‖ := by
    simp [Real.pi_pos.le, hx]
  rw [hcoef] at h
  have hle : ‖x‖ ^ n ≤ (2 * π * ‖x‖) ^ n := by
    apply pow_le_pow_left₀ (norm_nonneg x)
    have hp : 1 ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    nlinarith [norm_nonneg x]
  exact (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans h

/-- Copy of the host-private helper `HigherDimLQGMetric.fourier_symbol_basic_bound` (no kernel hypothesis). -/
private theorem fourier_symbol_basic_bound_seed (x : Rd d) :
    ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
      ∫ ζ : Rd d, |kernelSymbol κ ζ| := by
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ (Rd d))
    (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x
  change ‖VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Rd d))
      (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
      ∫ ζ : Rd d, |kernelSymbol κ ζ|
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

/-- Sign-free copy of `HigherDimLQGMetric.fourier_symbol_spatial_decay`. -/
theorem fourier_symbol_spatial_decay_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) (hn : n < 2 * d) :
    ∃ C : ℝ, ∀ x : Rd d,
      ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
        C * (1 + ‖x‖) ^ (-(n : ℝ)) := by
  let A : ℝ := ∫ ζ : Rd d, |kernelSymbol κ ζ|
  let B : ℝ := ∫ ζ : Rd d, ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖
  have hA : 0 ≤ A := integral_nonneg (fun _ => abs_nonneg _)
  have hB : 0 ≤ B := integral_nonneg (fun _ => norm_nonneg _)
  let C : ℝ := 2 ^ n * (A + B)
  refine ⟨C, fun x => ?_⟩
  have hr : 0 < 1 + ‖x‖ := by positivity
  have hpow : (1 + ‖x‖) ^ n *
      ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤ C := by
    by_cases hx : ‖x‖ ≤ 1
    · have hle : (1 + ‖x‖) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
      calc
        _ ≤ (2 : ℝ) ^ n *
            ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ ≤ 2 ^ n * A :=
          mul_le_mul_of_nonneg_left (fourier_symbol_basic_bound_seed x) (by positivity)
        _ ≤ C := by dsimp [C]; gcongr; linarith
    · have hx1 : 1 ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
      have hx0 : x ≠ 0 := by
        intro he
        have : (1 : ℝ) ≤ 0 := by simpa [he] using hx1
        linarith
      have hle : (1 + ‖x‖) ^ n ≤ (2 * ‖x‖) ^ n := by gcongr; linarith
      calc
        _ ≤ (2 * ‖x‖) ^ n *
            ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ ≤ 2 ^ n * B := by
          rw [mul_pow, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (fourier_symbol_spatial_pow_bound_seed hd hκ n hn x hx0) (by positivity)
        _ ≤ C := by dsimp [C]; gcongr; linarith
  have h : ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
      C / (1 + ‖x‖) ^ n := by
    exact (le_div_iff₀ (pow_pos hr n)).mpr (by
      simpa only [mul_comm] using hpow)
  simpa only [Real.rpow_neg hr.le, Real.rpow_natCast, div_eq_mul_inv] using h

/-- Sign-free copy of `HigherDimLQGMetric.convKernel_decay`. -/
theorem convKernel_decay_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∃ C : ℝ, ∀ x : Rd d,
      |convKernel κ x| ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
  obtain ⟨C, hC⟩ := fourier_symbol_spatial_decay_seed hd hκ (d + 1) (by omega)
  refine ⟨C, fun x => ?_⟩
  have h := hC (-x)
  rw [norm_neg] at h
  have heq : (convKernel κ x : ℂ) =
      𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) (-x) := by
    rw [convKernel_complex_eq_fourierInv]
    exact Real.fourierInv_eq_fourier_neg _ x
  rw [← heq] at h
  simpa only [Complex.norm_real, Nat.cast_add, Nat.cast_one, Real.norm_eq_abs] using h

/-- Sign-free copy of `HigherDimLQGMetric.integrable_convKernel`. -/
theorem integrable_convKernel_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) : Integrable (convKernel κ) := by
  obtain ⟨C, hC⟩ := convKernel_decay_seed hd hκ
  have hsource : Integrable (fun x : Rd d =>
      C * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by
    have hbase : Integrable (fun x : Rd d =>
        (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by
      apply integrable_one_add_norm (μ := volume)
      simp only [finrank_euclideanSpace_fin]
      norm_num
    exact hbase.const_mul C
  apply hsource.mono' (convKernel_contDiff_seed (by omega) hκ).continuous.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using hC x

end ConvKernelFourierDecay

section ConvKernelMain
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelMain`. -/

open MeasureTheory
open scoped FourierTransform
open HigherDimLFPP (Rd)

/-- **L1c** ([1] Rem. 1.1, Lemmas 2.9–2.10, the parts used later): `K` is smooth, integrable,
radial, `∫ K = 1`, `K̂ = kernelSymbol`, and `|K(x)| ≤ C (1+|x|)^{-(d+1)}` ([1] claims
`(1+|x|)^{1-2d}`, also true; `d+1` is all that is used).
Sign-free copy of `HigherDimLQGMetric.L1c_convKernel`. -/
def L1c_convKernel_seed : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPPAS.IsAdmissibleSeed κ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ Integrable (convKernel κ) ∧
    (∫ x, convKernel κ x = 1) ∧ (∀ x y : Rd d, ‖x‖ = ‖y‖ → convKernel κ x = convKernel κ y) ∧
    (∃ C : ℝ, ∀ x : Rd d, |convKernel κ x| ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) ∧
    𝓕 (fun x : Rd d => (convKernel κ x : ℂ)) = fun ζ => (kernelSymbol κ ζ : ℂ)

/-- The complete kernel result of packet L1c.
Sign-free copy of `HigherDimLQGMetric.l1c_convKernel`. -/
theorem l1c_convKernel_seed : L1c_convKernel_seed := by
  intro d hd κ hκ
  have hdp : 0 < d := by omega
  have hK : Integrable (convKernel κ) := integrable_convKernel_seed hd hκ
  exact ⟨convKernel_contDiff_seed hdp hκ, hK,
    convKernel_integral_eq_one_seed hdp hκ hK,
    fun _ _ h => convKernel_radial h,
    convKernel_decay_seed hd hκ,
    convKernel_fourier_eq_seed hdp hκ hK⟩

end ConvKernelMain

section CovKernelEps
/-! Copies from `HigherDimLQGMetric.Kernel.CovKernelEps`. -/

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.integrable_convKernelEps`. -/
theorem integrable_convKernelEps_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (convKernelEps κ ε) := by
  unfold convKernelEps
  exact ((integrable_convKernel_seed hd hκ).comp_smul (inv_ne_zero hε.ne')).const_mul _

/-- Sign-free copy of `HigherDimLQGMetric.integral_convKernelEps_eq_one`. -/
theorem integral_convKernelEps_eq_one_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x : Rd d, convKernelEps κ ε x = 1 := by
  unfold convKernelEps
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume (convKernel κ) hε.le,
    finrank_rd, smul_eq_mul,
    convKernel_integral_eq_one_seed (by omega) hκ (integrable_convKernel_seed hd hκ)]
  rw [mul_one, Real.rpow_neg (le_of_lt hε), Real.rpow_natCast]
  exact inv_mul_cancel₀ (pow_ne_zero _ hε.ne')

end CovKernelEps

section CovKernelMoment
/-! Copies from `HigherDimLQGMetric.Kernel.CovKernelMoment`. -/

open MeasureTheory
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Copy of the host-private helper `HigherDimLQGMetric.log_two_add_norm_le` (no kernel hypothesis). -/
private theorem log_two_add_norm_le_seed (x : Rd d) :
    Real.log (2 + ‖x‖) ≤
      4 * (1 + ‖x‖) ^ ((1 / 2 : ℝ)) := by
  have h := Real.log_le_rpow_div (x := 2 + ‖x‖) (by positivity)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hp : (2 + ‖x‖) ^ ((1 / 2 : ℝ)) ≤
      2 * (1 + ‖x‖) ^ ((1 / 2 : ℝ)) := by
    have hle : 2 + ‖x‖ ≤ 4 * (1 + ‖x‖) := by nlinarith [norm_nonneg x]
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 2 + ‖x‖) hle
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
      (by positivity : 0 ≤ 1 + ‖x‖)] at hr
    norm_num at hr ⊢
    exact hr
  calc
    Real.log (2 + ‖x‖) ≤ (2 + ‖x‖) ^ ((1 / 2 : ℝ)) / (1 / 2 : ℝ) := h
    _ = 2 * (2 + ‖x‖) ^ ((1 / 2 : ℝ)) := by ring
    _ ≤ 4 * (1 + ‖x‖) ^ ((1 / 2 : ℝ)) := by linarith

/-- Sign-free copy of `HigherDimLQGMetric.integrable_logMoment_convKernel`. -/
theorem integrable_logMoment_convKernel_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    Integrable (fun x : Rd d =>
      Real.log (2 + ‖x‖) * convKernel κ x) := by
  obtain ⟨C, hC⟩ := convKernel_decay_seed hd hκ
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbase : Integrable (fun x : Rd d =>
      4 * B * (1 + ‖x‖) ^ (-((d : ℝ) + 1 / 2))) := by
    have h : Integrable (fun x : Rd d =>
        (1 + ‖x‖) ^ (-((d : ℝ) + 1 / 2))) := by
      apply integrable_one_add_norm (μ := volume)
      simp only [finrank_euclideanSpace_fin]
      norm_num
    exact h.const_mul (4 * B)
  apply hbase.mono'
  · have hcont : Continuous (fun x : Rd d =>
        Real.log (2 + ‖x‖) * convKernel κ x) := by
      apply Continuous.mul
      · apply Continuous.log
        · fun_prop
        · intro x
          positivity
      · exact (convKernel_contDiff_seed (by omega) hκ).continuous
    exact hcont.aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    have hr : 0 < 1 + ‖x‖ := by positivity
    have hlog : 0 ≤ Real.log (2 + ‖x‖) :=
      Real.log_nonneg (by nlinarith [norm_nonneg x])
    have hK : |convKernel κ x| ≤
        B * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) :=
      (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog]
    calc
      Real.log (2 + ‖x‖) * |convKernel κ x| ≤
          Real.log (2 + ‖x‖) *
            (B * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by gcongr
      _ ≤ (4 * (1 + ‖x‖) ^ ((1 / 2 : ℝ))) *
            (B * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by
          gcongr
          exact log_two_add_norm_le_seed x
      _ = 4 * B * (1 + ‖x‖) ^ (-((d : ℝ) + 1 / 2)) := by
          calc
            _ = 4 * B * ((1 + ‖x‖) ^ ((1 / 2 : ℝ)) *
                (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by ring
            _ = _ := by
              rw [← Real.rpow_add hr]
              congr 1
              ring_nf

/-- Sign-free copy of `HigherDimLQGMetric.integrable_logMoment_convKernelEps`. -/
theorem integrable_logMoment_convKernelEps_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : Rd d =>
      Real.log (2 + ‖x‖) * convKernelEps κ ε x) := by
  let T : Rd d → Rd d := fun x => ε⁻¹ • x
  have hT : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hmain := ((integrable_logMoment_convKernel_seed hd hκ).comp_smul hT).const_mul
    (ε ^ (-(d : ℝ)))
  have hplain := ((integrable_convKernel_seed hd hκ).comp_smul hT).const_mul
    (Real.log (2 + ε) * ε ^ (-(d : ℝ)))
  apply (hmain.norm.add hplain.norm).mono'
  · have hc : Continuous (fun x : Rd d =>
        Real.log (2 + ‖x‖) * convKernelEps κ ε x) := by
      apply Continuous.mul
      · apply Continuous.log
        · fun_prop
        · intro x; positivity
      · exact continuous_const.mul
          ((convKernel_contDiff_seed (by omega) hκ).continuous.comp
            (continuous_const_smul _))
    exact hc.aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    have he : x = ε • T x := by
      dsimp [T]
      rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
    have hnorm : ‖x‖ = ε * ‖T x‖ := by
      calc
        ‖x‖ = ‖ε • T x‖ := congrArg norm he
        _ = _ := by simp [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hp : 2 + ‖x‖ ≤ (2 + ε) * (2 + ‖T x‖) := by
      rw [hnorm]
      nlinarith [norm_nonneg (T x)]
    have hlog : Real.log (2 + ‖x‖) ≤
        Real.log (2 + ‖T x‖) + Real.log (2 + ε) := by
      rw [← Real.log_mul (by positivity : 2 + ‖T x‖ ≠ 0)
        (by positivity : 2 + ε ≠ 0)]
      rw [mul_comm]
      exact Real.log_le_log (by positivity) hp
    have h0 : 0 ≤ Real.log (2 + ‖x‖) :=
      Real.log_nonneg (by nlinarith [norm_nonneg x])
    have h0' : 0 ≤ Real.log (2 + ‖T x‖) + Real.log (2 + ε) := by
      apply add_nonneg
      · exact Real.log_nonneg (by nlinarith [norm_nonneg (T x)])
      · exact Real.log_nonneg (by linarith)
    have hs : 0 ≤ ε ^ (-(d : ℝ)) := Real.rpow_nonneg hε.le _
    change |Real.log (2 + ‖x‖) * (ε ^ (-(d : ℝ)) * convKernel κ (T x))| ≤
      |ε ^ (-(d : ℝ)) * (Real.log (2 + ‖T x‖) * convKernel κ (T x))| +
        |Real.log (2 + ε) * ε ^ (-(d : ℝ)) * convKernel κ (T x)|
    rw [abs_mul, abs_of_nonneg h0, abs_mul, abs_of_nonneg hs]
    calc
      Real.log (2 + ‖x‖) * (ε ^ (-(d : ℝ)) * |convKernel κ (T x)|) ≤
        (Real.log (2 + ‖T x‖) + Real.log (2 + ε)) *
          (ε ^ (-(d : ℝ)) * |convKernel κ (T x)|) := by gcongr
      _ = |ε ^ (-(d : ℝ)) * (Real.log (2 + ‖T x‖) * convKernel κ (T x))| +
            |Real.log (2 + ε) * ε ^ (-(d : ℝ)) * convKernel κ (T x)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_nonneg hs,
            abs_of_nonneg (Real.log_nonneg (by nlinarith [norm_nonneg (T x)])),
            abs_of_nonneg (Real.log_nonneg (by linarith : 1 ≤ 2 + ε))]
          ring

end CovKernelMoment

end HigherDimLFPPAS.Signed
