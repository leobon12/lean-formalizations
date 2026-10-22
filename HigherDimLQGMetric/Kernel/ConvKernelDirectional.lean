import HigherDimLQGMetric.Kernel.ConvKernelIBP

/-!
# Directional symbol derivatives

Evaluation of the Fréchet derivatives along one fixed direction gives the derivatives
needed for A2.5. They are integrable through order `2d - 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Repeated derivative of the symbol along `v`, embedded in `ℂ`. -/
def directionalSymbol (κ : Rd d → ℝ) (v : Rd d) (n : ℕ)
    (ζ : Rd d) : ℂ :=
  ((iteratedFDeriv ℝ n (kernelSymbol κ) ζ) (fun _ => v) : ℝ)

theorem directionalSymbol_zero (v : Rd d) (ζ : Rd d) :
    directionalSymbol κ v 0 ζ = (kernelSymbol κ ζ : ℂ) := by
  simp [directionalSymbol]

theorem directionalSymbol_hasLineDerivAt (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (v : Rd d) (n : ℕ)
    {ζ : Rd d} (hζ : ζ ≠ 0) :
    HasLineDerivAt ℝ (directionalSymbol κ v n)
      (directionalSymbol κ v (n + 1) ζ) ζ v := by
  have hs : IsOpen ({0}ᶜ : Set (Rd d)) := isClosed_singleton.isOpen_compl
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (kernelSymbol κ) ζ :=
    (kernelSymbol_contDiffOn hd hκ).contDiffAt (hs.mem_nhds hζ)
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

theorem directionalSymbol_aestronglyMeasurable (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (v : Rd d) (n : ℕ) :
    AEStronglyMeasurable (directionalSymbol κ v n) volume := by
  let : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    simpa only [finrank_euclideanSpace_fin] using hd)
  have hderiv : ContinuousOn (iteratedFDeriv ℝ n (kernelSymbol κ))
      ({0}ᶜ : Set (Rd d)) :=
    ContinuousOn.continuousOn_iteratedFDeriv
      (kernelSymbol_contDiffOn hd hκ) (isClosed_singleton.isOpen_compl) (by simp)
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

theorem integrable_directionalSymbol (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (v : Rd d) (n : ℕ) (hnd : n < 2 * d) :
    Integrable (directionalSymbol κ v n) := by
  have hsource : Integrable (fun ζ : Rd d =>
      ‖v‖ ^ n * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖) := by
    simpa only [pow_zero, one_mul] using
      (integrable_kernelSymbol_iteratedFDeriv_moment hd hκ n 0 hnd).const_mul (‖v‖ ^ n)
  apply hsource.mono' (directionalSymbol_aestronglyMeasurable hd hκ v n)
  filter_upwards with ζ
  have hbound := ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ n (kernelSymbol κ) ζ) (fun _ : Fin n => v)
  have hprod : ∏ _ : Fin n, ‖v‖ = ‖v‖ ^ n := by simp
  simpa only [directionalSymbol, Complex.norm_real, ← Real.norm_eq_abs,
    hprod, mul_comm] using hbound

end HigherDimLQGMetric
