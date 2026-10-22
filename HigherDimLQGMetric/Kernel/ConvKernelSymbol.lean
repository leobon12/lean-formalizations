import HigherDimLQGMetric.Kernel.OneVarSymbolProfile
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Regularity of the convolution kernel symbol

The radial symbol `kernelSymbol κ` is smooth away from the origin and continuous everywhere.
This is the first part of MA5 A2.4, using the positive smooth one-variable profile proved in L1b.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The unsquared radial tail is smooth on the whole real line. -/
theorem symbolSq_contDiff (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symbolSq κ) := by
  rw [show symbolSq κ = (fun r => ∫ s in Ioi r, symbolDensity κ s) from
    funext (symbolSq_eq_integral_symbolDensity κ)]
  exact contDiff_integral_Ioi (contDiff_symbolDensity hd hκ)
    (integrableOn_Ioi_of_iteratedDeriv_decay (contDiff_symbolDensity hd hκ).continuous
      (symbolDensity_decay hd hκ))

/-- The variation of the radial tail from the origin is an ordinary interval integral. -/
theorem symbolSq_eq_one_sub_integral (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ρ : ℝ) :
    symbolSq κ ρ = 1 - ∫ s in (0 : ℝ)..ρ, symbolDensity κ s := by
  have hint := integrableOn_Ioi_of_iteratedDeriv_decay
    (contDiff_symbolDensity hd hκ).continuous (symbolDensity_decay hd hκ)
  have hadd := intervalIntegral.integral_interval_add_Ioi (hint 0) (hint ρ)
  rw [← symbolSq_eq_integral_symbolDensity κ, ← symbolSq_eq_integral_symbolDensity κ] at hadd
  rw [symbolSq_zero hd hκ] at hadd
  linarith only [hadd]

/-- The symbol is continuous, including at the origin. -/
theorem kernelSymbol_continuous (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Continuous (kernelSymbol κ) := by
  change Continuous (fun ζ : Rd d => Real.sqrt (symbolSq κ ‖ζ‖))
  exact Real.continuous_sqrt.comp ((symbolSq_contDiff hd hκ).continuous.comp continuous_norm)

/-- The symbol is smooth away from the origin. -/
theorem kernelSymbol_contDiffOn (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (kernelSymbol κ) ({0}ᶜ : Set (Rd d)) := by
  intro ζ hζ
  have hζ0 : ζ ≠ 0 := hζ
  have hnorm : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have hp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ => Real.sqrt (symbolSq κ r)) ‖ζ‖ :=
    (sqrt_symbolSq_contDiffOn hd hκ).contDiffAt (isOpen_Ioi.mem_nhds hnorm)
  have hn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Rd d => ‖z‖) ζ := contDiffAt_norm ℝ hζ0
  change ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : Rd d => Real.sqrt (symbolSq κ ‖z‖)) {0}ᶜ ζ
  exact (hp.comp ζ hn).contDiffWithinAt

/-- The symbol has value one at the origin. -/
theorem kernelSymbol_zero (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    kernelSymbol κ (0 : Rd d) = 1 := by
  rw [kernelSymbol_eq_sqrt_symbolSq, norm_zero, symbolSq_zero hd hκ, Real.sqrt_one]

/-- Rapid pointwise decay of the symbol outside the unit ball. -/
theorem kernelSymbol_decay (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (N : ℕ) : ∃ C : ℝ, ∀ ζ : Rd d, 1 ≤ ‖ζ‖ →
      ‖ζ‖ ^ N * |kernelSymbol κ ζ| ≤ C := by
  obtain ⟨C, hC⟩ := sqrt_symbolSq_decay hd hκ 0 N
  refine ⟨C, fun ζ hζ => ?_⟩
  simpa only [kernelSymbol_eq_sqrt_symbolSq, iteratedDeriv_zero] using hC ‖ζ‖ hζ

/-- A global uniform bound, combining compactness near zero and decay at infinity. -/
theorem kernelSymbol_bounded (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ C : ℝ, ∀ ζ : Rd d, |kernelSymbol κ ζ| ≤ C := by
  have hcompact : Bornology.IsBounded ((kernelSymbol κ) '' Metric.closedBall (0 : Rd d) 1) :=
    ((isCompact_closedBall (0 : Rd d) 1).image (kernelSymbol_continuous hd hκ)).isBounded
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_norm_le
  obtain ⟨C₁, hC₁⟩ := kernelSymbol_decay hd hκ 0
  refine ⟨max C₀ C₁, fun ζ => ?_⟩
  by_cases hζ : ‖ζ‖ ≤ 1
  · have hmem : kernelSymbol κ ζ ∈ (kernelSymbol κ) '' Metric.closedBall (0 : Rd d) 1 :=
      ⟨ζ, by simpa only [Metric.mem_closedBall, dist_zero_right] using hζ, rfl⟩
    exact (Real.norm_eq_abs _ ▸ hC₀ _ hmem).trans (le_max_left _ _)
  · have h := hC₁ ζ (le_of_lt (lt_of_not_ge hζ))
    simpa only [pow_zero, one_mul] using h.trans (le_max_right C₀ C₁)

/-- Every polynomially weighted symbol is bounded. -/
theorem kernelSymbol_pow_bounded (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (N : ℕ) : ∃ C : ℝ, ∀ ζ : Rd d, ‖ζ‖ ^ N * |kernelSymbol κ ζ| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := kernelSymbol_bounded hd hκ
  obtain ⟨C₁, hC₁⟩ := kernelSymbol_decay hd hκ N
  refine ⟨max C₀ C₁, fun ζ => ?_⟩
  by_cases hζ : ‖ζ‖ ≤ 1
  · calc
      ‖ζ‖ ^ N * |kernelSymbol κ ζ| ≤ 1 * |kernelSymbol κ ζ| :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hζ) (abs_nonneg _)
      _ = |kernelSymbol κ ζ| := one_mul _
      _ ≤ C₀ := hC₀ ζ
      _ ≤ max C₀ C₁ := le_max_left _ _
  · exact (hC₁ ζ (le_of_lt (lt_of_not_ge hζ))).trans (le_max_right _ _)

/-- The symbol has moments of every natural order. -/
theorem integrable_kernelSymbol_moment (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) :
    Integrable (fun ζ : Rd d => ‖ζ‖ ^ n * |kernelSymbol κ ζ|) := by
  obtain ⟨C₀, hC₀⟩ := kernelSymbol_bounded hd hκ
  obtain ⟨C₁, hC₁⟩ := kernelSymbol_pow_bounded hd hκ
    (n + (volume : Measure (Rd d)).integrablePower)
  exact integrable_of_le_of_pow_mul_le
    (μ := volume) (f := kernelSymbol κ) (k := n)
    (fun ζ => by simpa only [Real.norm_eq_abs] using hC₀ ζ)
    (fun ζ => by simpa only [Real.norm_eq_abs] using hC₁ ζ)
    (kernelSymbol_continuous hd hκ).aestronglyMeasurable

end HigherDimLQGMetric
