import HigherDimLQGMetric.Kernel.OneVarSymbol
import HigherDimLQGMetric.Kernel.OneVarSqrtTail

/-!
# The radial profile of `K̂`: `√G` is smooth on `(0, ∞)` and rapidly decreasing

Packet L1b (block B1), the bridge from the two targets to their consumer L1c (MA5 A2.2, last line:
"applied with `f(s) = |S| s^{d-1} k(s)²` and positivity from A2.3"). With
`symbolDensity κ s = |S^{d-1}| s^{d-1} |𝓕κ(s e₁)|²` we have `symbolSq κ x = ∫_x^∞ symbolDensity κ`
(`symbolSq_eq_integral_symbolDensity`), and `symbolDensity κ` satisfies every hypothesis of
`L1b_sqrtTail`: it is a Schwartz function on `ℝ` (`symbolDensitySchwartz`: `𝓕κ ∘ (t ↦ t e₁)` is Schwartz,
`|·|²` is a continuous real bilinear form, `s ↦ |S| s^{d-1}` has temperate growth), nonnegative on
`(0, ∞)`, with positive tails (`symbolSq_pos`). Hence (`sqrt_symbolSq_contDiffOn`,
`sqrt_symbolSq_decay`) the radial profile `x ↦ √(symbolSq κ x)` of the frozen `kernelSymbol κ` is smooth on
`(0, ∞)` and `sup_{x ≥ 1} x^N |(d/dx)^n √(symbolSq κ x)| < ∞` for all `n, N`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- The density `f(s) = |S^{d-1}| s^{d-1} |𝓕κ(s e₁)|²` of the tail `symbolSq κ x = ∫_x^∞ f`. -/
def symbolDensity (κ : Rd d → ℝ) (s : ℝ) : ℝ :=
  (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) * symbolIntegrand κ s

theorem symbolSq_eq_integral_symbolDensity (κ : Rd d → ℝ) (x : ℝ) :
    symbolSq κ x = ∫ s in Ioi x, symbolDensity κ s := by
  rw [symbolSq_eq, ← integral_const_mul]
  rfl

/-- The line `t ↦ t e₁` as a continuous linear map `ℝ →L[ℝ] ℝ^d`. -/
def lineE₁ (d : ℕ) : ℝ →L[ℝ] Rd d := (ContinuousLinearMap.id ℝ ℝ).smulRight (e₁ d)

theorem lineE₁_apply (t : ℝ) : lineE₁ d t = t • e₁ d := rfl

section Kernel

variable {κ : Rd d → ℝ}

/-- `t ↦ 𝓕κ(t e₁)` as a Schwartz function on `ℝ`. -/
def fourierKernelLine (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLM ℝ (g := lineE₁ d) (by fun_prop) ⟨1, 1, fun t => by
    simp only [lineE₁_apply, norm_smul, HigherDimLFPP.norm_e₁ hd, mul_one, pow_one, one_mul]
    linarith⟩ (𝓕 (kernelSchwartz hκ))

theorem fourierKernelLine_apply (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) (t : ℝ) :
    fourierKernelLine hd hκ t = 𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e₁ d) := by
  simp only [fourierKernelLine, SchwartzMap.compCLM_apply, Function.comp_apply]
  rw [coe_fourier_kernelSchwartz hκ]
  rfl

/-- `symbolDensity κ` as a Schwartz function on `ℝ`. -/
def symbolDensitySchwartz (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ
    (fun s : ℝ => (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) * s ^ (d - 1))
    (SchwartzMap.bilinLeftCLM (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      (fourierKernelLine hd hκ).hasTemperateGrowth (fourierKernelLine hd hκ))

theorem coe_symbolDensitySchwartz (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ⇑(symbolDensitySchwartz hd hκ) = symbolDensity κ := by
  funext s
  rw [symbolDensitySchwartz, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop),
    SchwartzMap.bilinLeftCLM_apply, smul_eq_mul, symbolDensity, symbolIntegrand]
  beta_reduce
  rw [fourierKernelLine_apply hd hκ]
  have : (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d))
      (𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d)) =
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d)‖ ^ 2 := by
    change inner ℝ (𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d))
      (𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d)) = _
    exact real_inner_self_eq_norm_sq _
  rw [this]
  ring

theorem contDiff_symbolDensity (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symbolDensity κ) := by
  rw [← coe_symbolDensitySchwartz hd hκ]
  exact (symbolDensitySchwartz hd hκ).smooth ⊤

/-- All derivatives of `symbolDensity κ` decay faster than any power (hypothesis of `L1b_sqrtTail`). -/
theorem symbolDensity_decay (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) (n N : ℕ) :
    ∃ C : ℝ, ∀ s, 1 ≤ s → s ^ N * |iteratedDeriv n (symbolDensity κ) s| ≤ C := by
  obtain ⟨C, _, hC⟩ := (symbolDensitySchwartz hd hκ).decay N n
  refine ⟨C, fun s hs => ?_⟩
  have h := hC s
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, coe_symbolDensitySchwartz hd hκ,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le one_pos hs)] at h
  exact h

theorem symbolDensity_nonneg (hd : 0 < d) {s : ℝ} (hs : 0 < s) : 0 ≤ symbolDensity κ s :=
  mul_nonneg (sphereConst_pos hd).le (symbolIntegrand_nonneg hs.le)

/-- **The radial profile of `K̂` is smooth on `(0, ∞)`** (L1b + L1a). -/
theorem sqrt_symbolSq_contDiffOn (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Real.sqrt (symbolSq κ x)) (Ioi 0) := by
  have h := (l1b_sqrtTail (symbolDensity κ) (contDiff_symbolDensity hd hκ)
    (fun s hs => symbolDensity_nonneg hd hs) (symbolDensity_decay hd hκ)
    (fun x _ => by rw [← symbolSq_eq_integral_symbolDensity]; exact symbolSq_pos hd hκ x)).1
  simp only [← symbolSq_eq_integral_symbolDensity] at h
  exact h

/-- **The radial profile of `K̂` is rapidly decreasing with all its derivatives** (L1b + L1a):
`sup_{x ≥ 1} x^N |(d/dx)^n √(symbolSq κ x)| < ∞`. -/
theorem sqrt_symbolSq_decay (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) (n N : ℕ) :
    ∃ C : ℝ, ∀ x, 1 ≤ x →
      x ^ N * |iteratedDeriv n (fun x => Real.sqrt (symbolSq κ x)) x| ≤ C := by
  have h := (l1b_sqrtTail (symbolDensity κ) (contDiff_symbolDensity hd hκ)
    (fun s hs => symbolDensity_nonneg hd hs) (symbolDensity_decay hd hκ)
    (fun x _ => by rw [← symbolSq_eq_integral_symbolDensity]; exact symbolSq_pos hd hκ x)).2 n N
  simp only [← symbolSq_eq_integral_symbolDensity] at h
  exact h

end Kernel

end HigherDimLQGMetric
