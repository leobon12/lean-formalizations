import HigherDimLQGMetric.Kernel.ConvKernelNearZeroSqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Local integrability of symbol derivatives

The A2.4 estimate implies local integrability of each derivative order
`n < 2d` by the Euclidean radial power criterion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Each positive-order symbol derivative of order less than `2d` is integrable near zero. -/
theorem integrableOn_kernelSymbol_iteratedFDeriv_near_zero (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) (hn : 0 < n)
    (hnd : n < 2 * d) :
    ∃ ρ : ℝ, 0 < ρ ∧
      IntegrableOn (iteratedFDeriv ℝ n (kernelSymbol κ))
        (Metric.ball (0 : Rd d) ρ) := by
  obtain ⟨ρ, hρ, hρ1, C, hC⟩ := kernelSymbol_iteratedFDeriv_near_zero hd hκ n hn
  refine ⟨ρ, hρ, ?_⟩
  let α : ℝ := (n : ℝ) - (d : ℝ)
  have hdim : 1 ≤ Module.finrank ℝ (Rd d) := by
    simpa using (show 1 ≤ d by omega)
  have hα : α < Module.finrank ℝ (Rd d) := by
    have hh : (n : ℝ) < 2 * (d : ℝ) := by exact_mod_cast hnd
    simpa only [α, finrank_euclideanSpace_fin] using (show (n : ℝ) - (d : ℝ) < d by linarith)
  let : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ (Rd d))
  have hcont : ContinuousOn (iteratedFDeriv ℝ n (kernelSymbol κ))
      ({0}ᶜ : Set (Rd d)) :=
    ContinuousOn.continuousOn_iteratedFDeriv
      (kernelSymbol_contDiffOn hd hκ) (isClosed_singleton.isOpen_compl) (by simp)
  have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ n (kernelSymbol κ)) volume := by
    have hh := hcont.aestronglyMeasurable (μ := volume)
      (isClosed_singleton.isOpen_compl.measurableSet)
    have hfull : volume.restrict ({0}ᶜ : Set (Rd d)) = volume :=
      Measure.restrict_eq_self_of_ae_mem (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
          (Measure.ae_ne volume (0 : Rd d)))
    rwa [hfull] at hh
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := C) (α := α)
    (r := ρ) hdim hα ?_ hmeas
  have hne : ∀ᵐ ζ : Rd d ∂volume.restrict (Metric.ball (0 : Rd d) ρ), ζ ≠ 0 :=
    ae_restrict_of_ae (Measure.ae_ne volume 0)
  have hmem : ∀ᵐ ζ : Rd d ∂volume.restrict (Metric.ball (0 : Rd d) ρ),
      ζ ∈ Metric.ball (0 : Rd d) ρ :=
    ae_restrict_mem₀ ((Metric.isOpen_ball.measurableSet : MeasurableSet
      (Metric.ball (0 : Rd d) ρ)).nullMeasurableSet)
  refine (hne.and hmem).mono ?_
  intro ζ hζpair
  rcases hζpair with ⟨hζ, hζmem⟩
  have hζρ : ‖ζ‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hζmem
  have hr : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have h : ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤ C * ‖ζ‖ ^ d / ‖ζ‖ ^ n := by
    apply (le_div_iff₀ (pow_pos hr n)).mpr
    simpa only [mul_comm] using hC ζ hζ hζρ
  have he : ‖ζ‖ ^ d / ‖ζ‖ ^ n = ‖ζ‖ ^ (-α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub_natCast hr.ne' (d : ℝ) n]
    congr 1
    dsimp [α]
    ring
  simpa only [he, mul_div_assoc] using h

end HigherDimLQGMetric
