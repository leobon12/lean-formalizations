import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLQGMetric.Kernel.OneVarFourier
import HigherDimLQGMetric.Kernel.OneVarSymbol
import HigherDimLQGMetric.Kernel.OneVarSymbolProfile
import HigherDimLQGMetric.Kernel.ConvKernelInfinity
import HigherDimLQGMetric.Kernel.ConvKernelSymbol
import HigherDimLQGMetric.Kernel.ConvKernelSmooth
import HigherDimLQGMetric.Kernel.ConvKernelZero
import HigherDimLQGMetric.Kernel.ConvKernelNearZero
import HigherDimLQGMetric.Kernel.ConvKernelDerivativeBounds
import HigherDimLQGMetric.Kernel.ConvKernelNearZeroSqrt
import HigherDimLQGMetric.Kernel.ConvKernelNearIntegrable

/-!
# Sign-free copies: the symbol `K̂ = kernelSymbol κ` and its derivatives

Packet G1 (ruling L7; planning audit `planning/audits/MA3-inputs.md` §4.1 and §4.3 items 1–2). The declarations of
`HigherDimLQGMetric.Kernel.OneVarFourier`, `HigherDimLQGMetric.Kernel.OneVarSymbol`,
`HigherDimLQGMetric.Kernel.OneVarSymbolProfile`, `HigherDimLQGMetric.Kernel.ConvKernelInfinity`,
`HigherDimLQGMetric.Kernel.ConvKernelSymbol`, `HigherDimLQGMetric.Kernel.ConvKernelSmooth`,
`HigherDimLQGMetric.Kernel.ConvKernelZero`, `HigherDimLQGMetric.Kernel.ConvKernelNearZero`,
`HigherDimLQGMetric.Kernel.ConvKernelDerivativeBounds`, `HigherDimLQGMetric.Kernel.ConvKernelNearZeroSqrt`,
`HigherDimLQGMetric.Kernel.ConvKernelNearIntegrable`
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

/-- Target 1 of packet G1: a nonnegative kernel seed of the repository is an admissible seed of the paper. -/
theorem _root_.HigherDimLFPP.IsLFPPKernel.toAdmissibleSeed {d : ℕ} {κ : HigherDimLFPP.Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) : HigherDimLFPPAS.IsAdmissibleSeed κ :=
  ⟨hκ.contDiff, hκ.hasCompactSupport, hκ.radial, hκ.integral_sq⟩

section OneVarFourier
/-! Copies from `HigherDimLQGMetric.Kernel.OneVarFourier`. -/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform RealInnerProductSpace
open HigherDimLFPP (Rd e₁)
variable {d : ℕ}
section Kernel
variable {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.contDiff_ofReal_kernel`. -/
theorem contDiff_ofReal_kernel_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Rd d => (κ x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hκ.contDiff

/-- Sign-free copy of `HigherDimLQGMetric.hasCompactSupport_ofReal_kernel`. -/
theorem hasCompactSupport_ofReal_kernel_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    HasCompactSupport (fun x : Rd d => (κ x : ℂ)) :=
  hκ.hasCompactSupport.comp_left Complex.ofReal_zero

/-- The complexified kernel `x ↦ (κ x : ℂ)` as a Schwartz function.
Sign-free copy of `HigherDimLQGMetric.kernelSchwartz`. -/
def kernelSchwartz_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) : SchwartzMap (Rd d) ℂ :=
  (hasCompactSupport_ofReal_kernel_seed hκ).toSchwartzMap (contDiff_ofReal_kernel_seed hκ)

/-- Sign-free copy of `HigherDimLQGMetric.kernelSchwartz_apply`. -/
theorem kernelSchwartz_apply_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (x : Rd d) :
    kernelSchwartz_seed hκ x = (κ x : ℂ) := rfl

/-- Sign-free copy of `HigherDimLQGMetric.coe_fourier_kernelSchwartz`. -/
theorem coe_fourier_kernelSchwartz_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ((𝓕 (kernelSchwartz_seed hκ) : SchwartzMap (Rd d) ℂ) : Rd d → ℂ) =
      𝓕 (fun x : Rd d => (κ x : ℂ)) := by
  rw [SchwartzMap.fourier_coe]
  rfl

/-- Sign-free copy of `HigherDimLQGMetric.continuous_fourier_kernel`. -/
theorem continuous_fourier_kernel_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    Continuous (𝓕 (fun x : Rd d => (κ x : ℂ))) := by
  rw [← coe_fourier_kernelSchwartz_seed hκ]
  exact (𝓕 (kernelSchwartz_seed hκ)).continuous

/-- Schwartz decay of `𝓕κ`: `‖ζ‖^k ‖𝓕κ(ζ)‖ ≤ C`.
Sign-free copy of `HigherDimLQGMetric.fourier_kernel_decay`. -/
theorem fourier_kernel_decay_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : Rd d, ‖ζ‖ ^ k * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) ζ‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := (𝓕 (kernelSchwartz_seed hκ)).decay k 0
  refine ⟨C, hC0, fun ζ => ?_⟩
  have := hC ζ
  rwa [norm_iteratedFDeriv_zero, coe_fourier_kernelSchwartz_seed hκ] at this

/-- **Plancherel**: `∫ ‖𝓕κ‖² = ∫ κ² = 1`.
Sign-free copy of `HigherDimLQGMetric.integral_norm_sq_fourier_kernel`. -/
theorem integral_norm_sq_fourier_kernel_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∫ ζ : Rd d, ‖𝓕 (fun x : Rd d => (κ x : ℂ)) ζ‖ ^ 2 = 1 := by
  have h := SchwartzMap.integral_norm_sq_fourier (kernelSchwartz_seed hκ)
  rw [coe_fourier_kernelSchwartz_seed hκ] at h
  rw [h, ← hκ.integral_sq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [kernelSchwartz_apply_seed, Complex.norm_real, Real.norm_eq_abs, sq_abs]
end Kernel

end OneVarFourier

section OneVarSymbol
/-! Copies from `HigherDimLQGMetric.Kernel.OneVarSymbol`. -/

open MeasureTheory Set Filter Topology
open scoped FourierTransform
open HigherDimLFPP (Rd e₁)
variable {d : ℕ}
section Kernel
variable {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.continuous_symbolIntegrand`. -/
theorem continuous_symbolIntegrand_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    Continuous (symbolIntegrand κ) := by
  have hF := continuous_fourier_kernel_seed hκ
  unfold symbolIntegrand
  fun_prop

/-- Decay of the integrand: `s² |φ(s)| ≤ C` for `s ≥ 1`.
Sign-free copy of `HigherDimLQGMetric.symbolIntegrand_decay`. -/
theorem symbolIntegrand_decay_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∃ C : ℝ, ∀ s, 1 ≤ s → s ^ 2 * |symbolIntegrand κ s| ≤ C := by
  obtain ⟨C₀, _, hC₀⟩ := fourier_kernel_decay_seed hκ 0
  obtain ⟨C₁, _, hC₁⟩ := fourier_kernel_decay_seed hκ (d + 1)
  refine ⟨C₁ * C₀, fun s hs => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hns : ‖s • e₁ d‖ = s := by
    rw [norm_smul, HigherDimLFPP.norm_e₁ hd, mul_one, Real.norm_eq_abs, abs_of_pos hs0]
  set F := ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d)‖ with hF
  have h0 : F ≤ C₀ := by have := hC₀ (s • e₁ d); rwa [pow_zero, one_mul] at this
  have h1 : s ^ (d + 1) * F ≤ C₁ := by have := hC₁ (s • e₁ d); rwa [hns] at this
  have hF0 : 0 ≤ F := norm_nonneg _
  unfold symbolIntegrand
  rw [← hF, abs_of_nonneg (by positivity)]
  have hpow : s ^ 2 * (s ^ (d - 1) * F ^ 2) = (s ^ (d + 1) * F) * F := by
    rw [show d + 1 = 2 + (d - 1) by omega, pow_add]
    ring
  rw [hpow]
  exact mul_le_mul h1 h0 hF0 ((mul_nonneg (by positivity) hF0).trans h1)

/-- Sign-free copy of `HigherDimLQGMetric.integrableOn_symbolIntegrand`. -/
theorem integrableOn_symbolIntegrand_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (a : ℝ) :
    IntegrableOn (symbolIntegrand κ) (Ioi a) := by
  obtain ⟨C, hC⟩ := symbolIntegrand_decay_seed hd hκ
  exact integrableOn_Ioi_of_decay (continuous_symbolIntegrand_seed hκ) hC a

/-- **`G(0) = 1`** (MA5 A2.1): polar coordinates and Plancherel.
Sign-free copy of `HigherDimLQGMetric.symbolSq_zero`. -/
theorem symbolSq_zero_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) : symbolSq κ 0 = 1 := by
  rw [← integral_norm_sq_fourier_kernel_seed hκ, integral_norm_sq_fourier_kernel_polar hd hκ.radial]
  rfl

/-- **`G(ρ) > 0` for `ρ ≥ 0`** (MA5 A2.3), integral form.
Sign-free copy of `HigherDimLQGMetric.integral_symbolIntegrand_pos`. -/
theorem integral_symbolIntegrand_pos_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : 0 < ∫ t in Ioi ρ, symbolIntegrand κ t := by
  have hint := integrableOn_symbolIntegrand_seed hd hκ ρ
  have hnn : ∀ t ∈ Ioi ρ, 0 ≤ symbolIntegrand κ t := fun t ht =>
    symbolIntegrand_nonneg (hρ.trans (le_of_lt ht))
  rcases (setIntegral_nonneg measurableSet_Ioi hnn).eq_or_lt with h0 | hpos
  · exfalso
    have hae : symbolIntegrand κ =ᵐ[volume.restrict (Ioi ρ)] 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae
        ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hnn)) hint).1 h0.symm
    have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
      (continuous_symbolIntegrand_seed hκ).continuousOn continuousOn_const
    have hfar : ∀ ζ : Rd d, ρ < ‖ζ‖ → 𝓕 (fun x : Rd d => (κ x : ℂ)) ζ = 0 := by
      intro ζ hζ
      have h1 : symbolIntegrand κ ‖ζ‖ = 0 := heq hζ
      unfold symbolIntegrand at h1
      have hpow : ‖ζ‖ ^ (d - 1) ≠ 0 := pow_ne_zero _ (by linarith)
      have h2 := (mul_eq_zero.1 h1).resolve_left hpow
      rw [fourier_kernel_eq_norm_smul_e₁ hd hκ.radial ζ]
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
    have hall := fourier_eq_zero_of_far hd (contDiff_ofReal_kernel_seed hκ).continuous
      (hasCompactSupport_ofReal_kernel_seed hκ) hfar
    have h1 := integral_norm_sq_fourier_kernel_seed hκ
    simp only [hall, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero] at h1
    exact zero_ne_one h1
  · exact hpos

/-- Sign-free copy of `HigherDimLQGMetric.symbolSq_pos_of_nonneg`. -/
theorem symbolSq_pos_of_nonneg_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : 0 < symbolSq κ ρ :=
  mul_pos (sphereConst_pos hd) (integral_symbolIntegrand_pos_seed hd hκ hρ)

/-- **`G(ρ) > 0` for every real `ρ`.**
Sign-free copy of `HigherDimLQGMetric.symbolSq_pos`. -/
theorem symbolSq_pos_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ρ : ℝ) :
    0 < symbolSq κ ρ := by
  rcases le_or_gt 0 ρ with hρ | hρ
  · exact symbolSq_pos_of_nonneg_seed hd hκ hρ
  rw [symbolSq_eq]
  refine mul_pos (sphereConst_pos hd) ?_
  have hint := integrableOn_symbolIntegrand_seed hd hκ
  have hsplit := intervalIntegral.integral_interval_add_Ioi (hint ρ) (hint 0)
  have hpos0 := integral_symbolIntegrand_pos_seed hd hκ (le_refl 0)
  rcases Nat.even_or_odd (d - 1) with hev | hodd
  · have : 0 ≤ ∫ t in ρ..0, symbolIntegrand κ t :=
      intervalIntegral.integral_nonneg hρ.le fun t _ => symbolIntegrand_nonneg_of_even hev t
    linarith
  · have hneg : ∫ t in ρ..0, symbolIntegrand κ t = -∫ t in (0 : ℝ)..(-ρ), symbolIntegrand κ t := by
      have h1 := intervalIntegral.integral_comp_neg (a := 0) (b := -ρ) (symbolIntegrand κ)
      rw [neg_neg, neg_zero] at h1
      rw [← h1, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => ?_
      exact symbolIntegrand_neg_of_odd hκ.radial hodd t
    have hsplit2 := intervalIntegral.integral_interval_add_Ioi (hint 0) (hint (-ρ))
    have hposρ := integral_symbolIntegrand_pos_seed hd hκ (le_of_lt (neg_pos.2 hρ))
    linarith
end Kernel

end OneVarSymbol

section OneVarSymbolProfile
/-! Copies from `HigherDimLQGMetric.Kernel.OneVarSymbolProfile`. -/

open MeasureTheory Set
open scoped FourierTransform
open HigherDimLFPP (Rd e₁)
variable {d : ℕ}
section Kernel
variable {κ : Rd d → ℝ}

/-- `t ↦ 𝓕κ(t e₁)` as a Schwartz function on `ℝ`.
Sign-free copy of `HigherDimLQGMetric.fourierKernelLine`. -/
def fourierKernelLine_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLM ℝ (g := lineE₁ d) (by fun_prop) ⟨1, 1, fun t => by
    simp only [lineE₁_apply, norm_smul, HigherDimLFPP.norm_e₁ hd, mul_one, pow_one, one_mul]
    linarith⟩ (𝓕 (kernelSchwartz_seed hκ))

/-- Sign-free copy of `HigherDimLQGMetric.fourierKernelLine_apply`. -/
theorem fourierKernelLine_apply_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (t : ℝ) :
    fourierKernelLine_seed hd hκ t = 𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e₁ d) := by
  simp only [fourierKernelLine_seed, SchwartzMap.compCLM_apply, Function.comp_apply]
  rw [coe_fourier_kernelSchwartz_seed hκ]
  rfl

/-- `symbolDensity κ` as a Schwartz function on `ℝ`.
Sign-free copy of `HigherDimLQGMetric.symbolDensitySchwartz`. -/
def symbolDensitySchwartz_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ
    (fun s : ℝ => (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) * s ^ (d - 1))
    (SchwartzMap.bilinLeftCLM (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      (fourierKernelLine_seed hd hκ).hasTemperateGrowth (fourierKernelLine_seed hd hκ))

/-- Sign-free copy of `HigherDimLQGMetric.coe_symbolDensitySchwartz`. -/
theorem coe_symbolDensitySchwartz_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ⇑(symbolDensitySchwartz_seed hd hκ) = symbolDensity κ := by
  funext s
  rw [symbolDensitySchwartz_seed, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop),
    SchwartzMap.bilinLeftCLM_apply, smul_eq_mul, symbolDensity, symbolIntegrand]
  beta_reduce
  rw [fourierKernelLine_apply_seed hd hκ]
  have : (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d))
      (𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d)) =
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d)‖ ^ 2 := by
    change inner ℝ (𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d))
      (𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d)) = _
    exact real_inner_self_eq_norm_sq _
  rw [this]
  ring

/-- Sign-free copy of `HigherDimLQGMetric.contDiff_symbolDensity`. -/
theorem contDiff_symbolDensity_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symbolDensity κ) := by
  rw [← coe_symbolDensitySchwartz_seed hd hκ]
  exact (symbolDensitySchwartz_seed hd hκ).smooth ⊤

/-- All derivatives of `symbolDensity κ` decay faster than any power (hypothesis of `L1b_sqrtTail`).
Sign-free copy of `HigherDimLQGMetric.symbolDensity_decay`. -/
theorem symbolDensity_decay_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n N : ℕ) :
    ∃ C : ℝ, ∀ s, 1 ≤ s → s ^ N * |iteratedDeriv n (symbolDensity κ) s| ≤ C := by
  obtain ⟨C, _, hC⟩ := (symbolDensitySchwartz_seed hd hκ).decay N n
  refine ⟨C, fun s hs => ?_⟩
  have h := hC s
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, coe_symbolDensitySchwartz_seed hd hκ,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le one_pos hs)] at h
  exact h

/-- **The radial profile of `K̂` is smooth on `(0, ∞)`** (L1b + L1a).
Sign-free copy of `HigherDimLQGMetric.sqrt_symbolSq_contDiffOn`. -/
theorem sqrt_symbolSq_contDiffOn_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Real.sqrt (symbolSq κ x)) (Ioi 0) := by
  have h := (l1b_sqrtTail (symbolDensity κ) (contDiff_symbolDensity_seed hd hκ)
    (fun s hs => symbolDensity_nonneg hd hs) (symbolDensity_decay_seed hd hκ)
    (fun x _ => by rw [← symbolSq_eq_integral_symbolDensity]; exact symbolSq_pos_seed hd hκ x)).1
  simp only [← symbolSq_eq_integral_symbolDensity] at h
  exact h

/-- **The radial profile of `K̂` is rapidly decreasing with all its derivatives** (L1b + L1a):
`sup_{x ≥ 1} x^N |(d/dx)^n √(symbolSq κ x)| < ∞`.
Sign-free copy of `HigherDimLQGMetric.sqrt_symbolSq_decay`. -/
theorem sqrt_symbolSq_decay_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n N : ℕ) :
    ∃ C : ℝ, ∀ x, 1 ≤ x →
      x ^ N * |iteratedDeriv n (fun x => Real.sqrt (symbolSq κ x)) x| ≤ C := by
  have h := (l1b_sqrtTail (symbolDensity κ) (contDiff_symbolDensity_seed hd hκ)
    (fun s hs => symbolDensity_nonneg hd hs) (symbolDensity_decay_seed hd hκ)
    (fun x _ => by rw [← symbolSq_eq_integral_symbolDensity]; exact symbolSq_pos_seed hd hκ x)).2 n N
  simp only [← symbolSq_eq_integral_symbolDensity] at h
  exact h
end Kernel

end OneVarSymbolProfile

section ConvKernelInfinity
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelInfinity`. -/

open Set MeasureTheory
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.radial_deriv_uniform_decay`. -/
private theorem radial_deriv_uniform_decay_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n M : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i ≤ n, ∀ r : ℝ, 1 ≤ r →
      ‖iteratedFDeriv ℝ i (fun t : ℝ => Real.sqrt (symbolSq κ t)) r‖ ≤
        B * r ^ (-(M : ℝ)) := by
  have hh (i : ℕ) : ∃ C : ℝ, ∀ r ∈ Ici (1 : ℝ),
      ‖iteratedFDeriv ℝ i (fun t : ℝ => Real.sqrt (symbolSq κ t)) r‖ ≤
        C * r ^ (-(M : ℝ)) := by
    obtain ⟨C, hC⟩ := sqrt_symbolSq_decay_seed hd hκ i M
    refine ⟨C, fun r hr => ?_⟩
    have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
    have h : |iteratedDeriv i (fun t : ℝ => Real.sqrt (symbolSq κ t)) r| ≤
        C / r ^ M := by
      apply (le_div_iff₀ (pow_pos hr0 M)).mpr
      simpa only [mul_comm] using hC r hr
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      Real.rpow_neg hr0.le, Real.rpow_natCast, div_eq_mul_inv] using h
  obtain ⟨B, hB, hBi⟩ := finite_uniform_weighted_bound
    (fun i r => ‖iteratedFDeriv ℝ i (fun t : ℝ => Real.sqrt (symbolSq κ t)) r‖)
    (fun r : ℝ => r ^ (-(M : ℝ))) (Ici (1 : ℝ))
    (fun r hr => Real.rpow_nonneg (by linarith [show 1 ≤ r from hr]) _)
    hh n
  exact ⟨B, hB, fun i hi r hr => hBi i hi r hr⟩

/-- Copy of the host-private helper `HigherDimLQGMetric.norm_deriv_uniform_outside` (no kernel hypothesis). -/
private theorem norm_deriv_uniform_outside_seed (d n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i : ℕ, 1 ≤ i → i ≤ n → ∀ x : Rd d,
      1 ≤ ‖x‖ → ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖ ≤ A := by
  have hh (i : ℕ) : ∃ C : ℝ, ∀ x ∈ {x : Rd d | 1 ≤ ‖x‖},
      (if i = 0 then 0 else ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖) ≤ C := by
    by_cases hi : i = 0
    · exact ⟨0, fun x hx => by simp [hi]⟩
    · obtain ⟨C, hC⟩ := norm_pow_deriv_weighted (dim := d) 1 i
      refine ⟨C, fun x hx => ?_⟩
      have hr : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num) hx
      have hx0 : x ≠ 0 := norm_pos_iff.mp hr
      have hw := hC x hx0
      simp only [pow_one] at hw
      have hrpow : ‖x‖ ≤ ‖x‖ ^ i := le_self_pow₀ hx hi
      have hle : ‖x‖ * ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖ ≤
          ‖x‖ * C := by
        calc
          ‖x‖ * ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖ ≤
              ‖x‖ ^ i * ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖ :=
            mul_le_mul_of_nonneg_right hrpow (norm_nonneg _)
          _ ≤ C * ‖x‖ := hw
          _ = ‖x‖ * C := mul_comm _ _
      simpa [hi] using le_of_mul_le_mul_left hle hr
  obtain ⟨A, hA, hAi⟩ := finite_uniform_bound
    (fun i (x : Rd d) => if i = 0 then 0 else
      ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖)
    {x : Rd d | 1 ≤ ‖x‖} hh n
  refine ⟨A, hA, fun i hi hin x hx => ?_⟩
  simpa [Nat.ne_of_gt hi] using hAi i hin x hx

/-- Sign-free copy of `HigherDimLQGMetric.kernelSymbol_iteratedFDeriv_decay`. -/
theorem kernelSymbol_iteratedFDeriv_decay_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n M : ℕ) :
    ∃ C : ℝ, ∀ ζ : Rd d, 1 ≤ ‖ζ‖ →
      ‖ζ‖ ^ M * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤ C := by
  obtain ⟨A, hA, hAi⟩ := norm_deriv_uniform_outside_seed d n
  obtain ⟨B, hB, hBi⟩ := radial_deriv_uniform_decay_seed hd hκ n M
  let C : ℝ := (n.factorial : ℝ) * B * A ^ n
  refine ⟨C, fun ζ hζ => ?_⟩
  have hζ0 : ζ ≠ 0 := by
    intro he
    have : (1 : ℝ) ≤ 0 := by simpa [he] using hζ
    linarith
  have hnorm0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have hs : IsOpen ({0}ᶜ : Set (Rd d)) := isClosed_singleton.isOpen_compl
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Rd d => ‖z‖) ({0}ᶜ : Set (Rd d)) := by
    intro z hz
    exact (contDiffAt_norm ℝ (show z ≠ 0 from hz)).contDiffWithinAt
  have hmap : MapsTo (fun z : Rd d => ‖z‖) ({0}ᶜ : Set (Rd d)) (Ioi 0) := by
    intro z hz
    exact norm_pos_iff.mpr hz
  have houter : ∀ i ≤ n,
      ‖iteratedFDerivWithin ℝ i (fun t : ℝ => Real.sqrt (symbolSq κ t))
        (Ioi 0) ‖ζ‖‖ ≤ B * ‖ζ‖ ^ (-(M : ℝ)) := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi hnorm0]
    exact hBi i hi ‖ζ‖ hζ
  have hinner : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun z : Rd d => ‖z‖)
        ({0}ᶜ : Set (Rd d)) ζ‖ ≤ A ^ i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hs hζ0]
    exact (hAi i hi hin ζ hζ).trans (le_self_pow₀ hA (Nat.ne_of_gt hi))
  have hc := norm_iteratedFDerivWithin_comp_le (sqrt_symbolSq_contDiffOn_seed hd hκ)
    hf (by simp : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)) isOpen_Ioi.uniqueDiffOn
    hs.uniqueDiffOn hmap hζ0 houter hinner
  rw [iteratedFDerivWithin_of_isOpen n hs hζ0] at hc
  have heq : ((fun t : ℝ => Real.sqrt (symbolSq κ t)) ∘
      (fun z : Rd d => ‖z‖)) = kernelSymbol κ := by
    funext z
    exact (kernelSymbol_eq_sqrt_symbolSq (κ := κ) z).symm
  rw [heq] at hc
  have hpow : ‖ζ‖ ^ M * ‖ζ‖ ^ (-(M : ℝ)) = 1 := by
    rw [Real.rpow_neg hnorm0.le, Real.rpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero M hnorm0.ne')
  have hh := mul_le_mul_of_nonneg_left hc (pow_nonneg hnorm0.le M)
  calc
    ‖ζ‖ ^ M * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤
        ‖ζ‖ ^ M * ((n.factorial : ℝ) * (B * ‖ζ‖ ^ (-(M : ℝ))) * A ^ n) := hh
    _ = C := by
      calc
        _ = ((n.factorial : ℝ) * B * A ^ n) *
            (‖ζ‖ ^ M * ‖ζ‖ ^ (-(M : ℝ))) := by ring
        _ = C := by rw [hpow, mul_one]

end ConvKernelInfinity

section ConvKernelSymbol
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelSymbol`. -/

open MeasureTheory Set
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- The unsquared radial tail is smooth on the whole real line.
Sign-free copy of `HigherDimLQGMetric.symbolSq_contDiff`. -/
theorem symbolSq_contDiff_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symbolSq κ) := by
  rw [show symbolSq κ = (fun r => ∫ s in Ioi r, symbolDensity κ s) from
    funext (symbolSq_eq_integral_symbolDensity κ)]
  exact contDiff_integral_Ioi (contDiff_symbolDensity_seed hd hκ)
    (integrableOn_Ioi_of_iteratedDeriv_decay (contDiff_symbolDensity_seed hd hκ).continuous
      (symbolDensity_decay_seed hd hκ))

/-- The variation of the radial tail from the origin is an ordinary interval integral.
Sign-free copy of `HigherDimLQGMetric.symbolSq_eq_one_sub_integral`. -/
theorem symbolSq_eq_one_sub_integral_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ρ : ℝ) :
    symbolSq κ ρ = 1 - ∫ s in (0 : ℝ)..ρ, symbolDensity κ s := by
  have hint := integrableOn_Ioi_of_iteratedDeriv_decay
    (contDiff_symbolDensity_seed hd hκ).continuous (symbolDensity_decay_seed hd hκ)
  have hadd := intervalIntegral.integral_interval_add_Ioi (hint 0) (hint ρ)
  rw [← symbolSq_eq_integral_symbolDensity κ, ← symbolSq_eq_integral_symbolDensity κ] at hadd
  rw [symbolSq_zero_seed hd hκ] at hadd
  linarith only [hadd]

/-- The symbol is continuous, including at the origin.
Sign-free copy of `HigherDimLQGMetric.kernelSymbol_continuous`. -/
theorem kernelSymbol_continuous_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    Continuous (kernelSymbol κ) := by
  change Continuous (fun ζ : Rd d => Real.sqrt (symbolSq κ ‖ζ‖))
  exact Real.continuous_sqrt.comp ((symbolSq_contDiff_seed hd hκ).continuous.comp continuous_norm)

/-- The symbol is smooth away from the origin.
Sign-free copy of `HigherDimLQGMetric.kernelSymbol_contDiffOn`. -/
theorem kernelSymbol_contDiffOn_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (kernelSymbol κ) ({0}ᶜ : Set (Rd d)) := by
  intro ζ hζ
  have hζ0 : ζ ≠ 0 := hζ
  have hnorm : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have hp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ => Real.sqrt (symbolSq κ r)) ‖ζ‖ :=
    (sqrt_symbolSq_contDiffOn_seed hd hκ).contDiffAt (isOpen_Ioi.mem_nhds hnorm)
  have hn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Rd d => ‖z‖) ζ := contDiffAt_norm ℝ hζ0
  change ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : Rd d => Real.sqrt (symbolSq κ ‖z‖)) {0}ᶜ ζ
  exact (hp.comp ζ hn).contDiffWithinAt

/-- The symbol has value one at the origin.
Sign-free copy of `HigherDimLQGMetric.kernelSymbol_zero`. -/
theorem kernelSymbol_zero_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    kernelSymbol κ (0 : Rd d) = 1 := by
  rw [kernelSymbol_eq_sqrt_symbolSq, norm_zero, symbolSq_zero_seed hd hκ, Real.sqrt_one]

/-- Rapid pointwise decay of the symbol outside the unit ball.
Sign-free copy of `HigherDimLQGMetric.kernelSymbol_decay`. -/
theorem kernelSymbol_decay_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (N : ℕ) : ∃ C : ℝ, ∀ ζ : Rd d, 1 ≤ ‖ζ‖ →
      ‖ζ‖ ^ N * |kernelSymbol κ ζ| ≤ C := by
  obtain ⟨C, hC⟩ := sqrt_symbolSq_decay_seed hd hκ 0 N
  refine ⟨C, fun ζ hζ => ?_⟩
  simpa only [kernelSymbol_eq_sqrt_symbolSq, iteratedDeriv_zero] using hC ‖ζ‖ hζ

/-- A global uniform bound, combining compactness near zero and decay at infinity.
Sign-free copy of `HigherDimLQGMetric.kernelSymbol_bounded`. -/
theorem kernelSymbol_bounded_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∃ C : ℝ, ∀ ζ : Rd d, |kernelSymbol κ ζ| ≤ C := by
  have hcompact : Bornology.IsBounded ((kernelSymbol κ) '' Metric.closedBall (0 : Rd d) 1) :=
    ((isCompact_closedBall (0 : Rd d) 1).image (kernelSymbol_continuous_seed hd hκ)).isBounded
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_norm_le
  obtain ⟨C₁, hC₁⟩ := kernelSymbol_decay_seed hd hκ 0
  refine ⟨max C₀ C₁, fun ζ => ?_⟩
  by_cases hζ : ‖ζ‖ ≤ 1
  · have hmem : kernelSymbol κ ζ ∈ (kernelSymbol κ) '' Metric.closedBall (0 : Rd d) 1 :=
      ⟨ζ, by simpa only [Metric.mem_closedBall, dist_zero_right] using hζ, rfl⟩
    exact (Real.norm_eq_abs _ ▸ hC₀ _ hmem).trans (le_max_left _ _)
  · have h := hC₁ ζ (le_of_lt (lt_of_not_ge hζ))
    simpa only [pow_zero, one_mul] using h.trans (le_max_right C₀ C₁)

/-- Every polynomially weighted symbol is bounded.
Sign-free copy of `HigherDimLQGMetric.kernelSymbol_pow_bounded`. -/
theorem kernelSymbol_pow_bounded_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (N : ℕ) : ∃ C : ℝ, ∀ ζ : Rd d, ‖ζ‖ ^ N * |kernelSymbol κ ζ| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := kernelSymbol_bounded_seed hd hκ
  obtain ⟨C₁, hC₁⟩ := kernelSymbol_decay_seed hd hκ N
  refine ⟨max C₀ C₁, fun ζ => ?_⟩
  by_cases hζ : ‖ζ‖ ≤ 1
  · calc
      ‖ζ‖ ^ N * |kernelSymbol κ ζ| ≤ 1 * |kernelSymbol κ ζ| :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hζ) (abs_nonneg _)
      _ = |kernelSymbol κ ζ| := one_mul _
      _ ≤ C₀ := hC₀ ζ
      _ ≤ max C₀ C₁ := le_max_left _ _
  · exact (hC₁ ζ (le_of_lt (lt_of_not_ge hζ))).trans (le_max_right _ _)

/-- The symbol has moments of every natural order.
Sign-free copy of `HigherDimLQGMetric.integrable_kernelSymbol_moment`. -/
theorem integrable_kernelSymbol_moment_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) :
    Integrable (fun ζ : Rd d => ‖ζ‖ ^ n * |kernelSymbol κ ζ|) := by
  obtain ⟨C₀, hC₀⟩ := kernelSymbol_bounded_seed hd hκ
  obtain ⟨C₁, hC₁⟩ := kernelSymbol_pow_bounded_seed hd hκ
    (n + (volume : Measure (Rd d)).integrablePower)
  exact integrable_of_le_of_pow_mul_le
    (μ := volume) (f := kernelSymbol κ) (k := n)
    (fun ζ => by simpa only [Real.norm_eq_abs] using hC₀ ζ)
    (fun ζ => by simpa only [Real.norm_eq_abs] using hC₁ ζ)
    (kernelSymbol_continuous_seed hd hκ).aestronglyMeasurable

end ConvKernelSymbol

section ConvKernelSmooth
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelSmooth`. -/

open MeasureTheory
open scoped FourierTransform ComplexConjugate
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- All natural moments of the complex embedding of `kernelSymbol` are integrable.
Sign-free copy of `HigherDimLQGMetric.integrable_kernelSymbol_complex_moment`. -/
theorem integrable_kernelSymbol_complex_moment_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) :
    Integrable (fun ζ : Rd d => ‖ζ‖ ^ n * ‖(kernelSymbol κ ζ : ℂ)‖) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    integrable_kernelSymbol_moment_seed hd hκ n

/-- The inverse Fourier kernel is smooth.
Sign-free copy of `HigherDimLQGMetric.convKernel_contDiff`. -/
theorem convKernel_contDiff_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) := by
  let o : Rd d → ℂ := fun ζ => (kernelSymbol κ ζ : ℂ)
  have hfour : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓕 o) :=
    Real.contDiff_fourier (fun n _ => integrable_kernelSymbol_complex_moment_seed hd hκ n)
  have hinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓕⁻ o) := by
    have h := hfour.comp (contDiff_id.neg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Rd d => -x))
    convert h using 1
    funext x
    exact Real.fourierInv_eq_fourier_neg o x
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (𝓕⁻ o x).re)
  exact Complex.reCLM.contDiff.comp hinv

end ConvKernelSmooth

section ConvKernelZero
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelZero`. -/

open MeasureTheory Set Filter
open scoped FourierTransform Topology
open HigherDimLFPP (Rd e₁)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.symbolAux_eq_line`. -/
theorem symbolAux_eq_line_seed (hd : 0 < d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (ζ : Rd d) : symbolAux κ ζ = symbolAuxLine κ ‖ζ‖ := by
  unfold symbolAux symbolAuxLine
  apply intervalIntegral.integral_congr
  intro u _
  dsimp
  have hnorm : ‖u • ζ‖ = ‖(‖ζ‖ * u) • e₁ d‖ := by
    rw [norm_smul, norm_smul, HigherDimLFPP.norm_e₁ hd, mul_one]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg ζ)]
    ring
  rw [fourier_kernel_eq_of_norm_eq hκ.radial hnorm]

/-- Exact identity `G(ρ) = 1 - ρ ∫₀¹ f(ρu) du`, valid even for negative `ρ`.
Sign-free copy of `HigherDimLQGMetric.symbolSq_eq_one_sub_mul_average`. -/
theorem symbolSq_eq_one_sub_mul_average_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ρ : ℝ) :
    symbolSq κ ρ = 1 - ρ * symbolAverage κ ρ := by
  rw [symbolSq_eq_one_sub_integral_seed hd hκ]
  have h := intervalIntegral.smul_integral_comp_mul_left
    (f := symbolDensity κ) ρ (a := (0 : ℝ)) (b := (1 : ℝ))
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [← h]
  rfl

/-- The A2.4 identity on the radial line, with no restriction on the sign of `ρ`.
Sign-free copy of `HigherDimLQGMetric.symbolSq_eq_one_sub_pow_auxLine`. -/
theorem symbolSq_eq_one_sub_pow_auxLine_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ρ : ℝ) :
    symbolSq κ ρ = 1 - ρ ^ d * symbolAuxLine κ ρ := by
  rw [symbolSq_eq_one_sub_mul_average_seed hd hκ,
    symbolAverage_eq_pow_mul_auxLine κ ρ]
  congr 1
  calc
    ρ * (ρ ^ (d - 1) * symbolAuxLine κ ρ) =
        ρ ^ ((d - 1) + 1) * symbolAuxLine κ ρ := by rw [pow_succ]; ring
    _ = ρ ^ d * symbolAuxLine κ ρ := by rw [Nat.sub_add_cancel hd]

/-- The exact multivariable A2.4 factorization, prior to regularity bounds.
Sign-free copy of `HigherDimLQGMetric.kernelSymbol_sq_eq_one_sub_pow_aux`. -/
theorem kernelSymbol_sq_eq_one_sub_pow_aux_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ζ : Rd d) :
    symbolSq κ ‖ζ‖ = 1 - ‖ζ‖ ^ d * symbolAux κ ζ := by
  rw [symbolSq_eq_one_sub_pow_auxLine_seed hd hκ, symbolAux_eq_line_seed hd hκ]

/-- The auxiliary in the exact A2.4 factorization is smooth on all of Euclidean space.
Sign-free copy of `HigherDimLQGMetric.symbolAux_contDiff`. -/
theorem symbolAux_contDiff_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symbolAux κ) := by
  let f : Rd d → ℝ → ℝ := fun ζ u =>
    (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
      u ^ (d - 1) *
      Complex.normSq (𝓕 (fun x : Rd d => (κ x : ℂ)) (u • ζ))
  have hFour : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Rd d × ℝ => 𝓕 (fun x : Rd d => (κ x : ℂ)) (p.2 • p.1)) := by
    have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (𝓕 (fun x : Rd d => (κ x : ℂ))) := by
      rw [← coe_fourier_kernelSchwartz_seed hκ]
      exact (𝓕 (kernelSchwartz_seed hκ)).smooth ⊤
    exact hh.comp (contDiff_snd.smul contDiff_fst)
  have hNormSq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Rd d × ℝ => Complex.normSq
        (𝓕 (fun x : Rd d => (κ x : ℂ)) (p.2 • p.1))) := by
    have hr := Complex.reCLM.contDiff.comp hFour
    have hi := Complex.imCLM.contDiff.comp hFour
    simpa only [Complex.normSq_apply, Function.comp_apply, pow_two,
      Complex.reCLM_apply, Complex.imCLM_apply] using (hr.pow 2).add (hi.pow 2)
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f.uncurry := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Rd d × ℝ =>
        (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
          p.2 ^ (d - 1) *
          Complex.normSq (𝓕 (fun x : Rd d => (κ x : ℂ)) (p.2 • p.1)))
    exact (contDiff_const.mul (contDiff_snd.pow _)).mul hNormSq
  have h := contDiff_setIntegral_Icc_of_contDiff f hf
  convert h using 1
  funext ζ
  simp only [symbolAux, f, Complex.normSq_eq_norm_sq,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]

/-- Every derivative of the smooth auxiliary is bounded on the closed unit ball.
Sign-free copy of `HigherDimLQGMetric.symbolAux_iteratedFDeriv_bounded`. -/
theorem symbolAux_iteratedFDeriv_bounded_seed (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (n : ℕ) : ∃ C : ℝ, ∀ ζ : Rd d, ‖ζ‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (symbolAux κ) ζ‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ n (symbolAux κ)) :=
    (symbolAux_contDiff_seed hκ).continuous_iteratedFDeriv (by simp)
  have hb : Bornology.IsBounded
      ((iteratedFDeriv ℝ n (symbolAux κ)) '' Metric.closedBall (0 : Rd d) 1) :=
    ((isCompact_closedBall (0 : Rd d) 1).image hc).isBounded
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  exact ⟨C, fun ζ hζ => hC _ ⟨ζ, by simpa only [Metric.mem_closedBall, dist_zero_right] using hζ,
    rfl⟩⟩

/-- On a fixed neighborhood of zero, the A2.4 perturbation is at most one half.
Sign-free copy of `HigherDimLQGMetric.symbolAux_small_near_zero`. -/
theorem symbolAux_small_near_zero_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ ζ : Rd d, ‖ζ‖ < ρ →
      |‖ζ‖ ^ d * symbolAux κ ζ| ≤ 1 / 2 := by
  let p : Rd d → ℝ := fun ζ => ‖ζ‖ ^ d * symbolAux κ ζ
  have hp : ContinuousAt p 0 :=
    ((continuous_norm.pow d).mul (symbolAux_contDiff_seed hκ).continuous).continuousAt
  have hp0 : p 0 = 0 := by simp [p, Nat.ne_of_gt hd]
  have he : ∀ᶠ ζ in 𝓝 (0 : Rd d), |p ζ| < 1 / 2 := by
    have h := hp.abs.eventually_lt
      (continuousAt_const : ContinuousAt (fun _ : Rd d => (1 / 2 : ℝ)) 0)
      (by norm_num [hp0])
    exact h
  rcases Metric.mem_nhds_iff.mp he with ⟨ε, hε, hball⟩
  refine ⟨min ε 1, lt_min hε (by norm_num), min_le_right ε 1, fun ζ hζ => ?_⟩
  have hz : ζ ∈ Metric.ball (0 : Rd d) ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using lt_of_lt_of_le hζ (min_le_left ε 1)
  exact le_of_lt (hball hz)

end ConvKernelZero

section ConvKernelNearZero
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelNearZero`. -/

open MeasureTheory Set
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Weighted `n`th derivative estimate for the A2.4 perturbation.
Sign-free copy of `HigherDimLQGMetric.symbolPerturb_iteratedFDeriv_weighted`. -/
theorem symbolPerturb_iteratedFDeriv_weighted_seed
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) :
    ∃ C : ℝ, ∀ ζ : Rd d, ζ ≠ 0 → ‖ζ‖ ≤ 1 →
      ‖ζ‖ ^ n * ‖iteratedFDeriv ℝ n
        (fun z : Rd d => ‖z‖ ^ d * symbolAux κ z) ζ‖ ≤ C * ‖ζ‖ ^ d := by
  let f : Rd d → ℝ := fun z => ‖z‖ ^ d
  let g : Rd d → ℝ := symbolAux κ
  let Cp : ℕ → ℝ := fun i => max (Classical.choose (norm_pow_deriv_weighted (dim := d) d i)) 0
  let Cg : ℕ → ℝ := fun j => max (Classical.choose (symbolAux_iteratedFDeriv_bounded_seed hκ j)) 0
  have hCp (i : ℕ) (x : Rd d) (hx : x ≠ 0) :
      ‖x‖ ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ Cp i * ‖x‖ ^ d := by
    exact (Classical.choose_spec (norm_pow_deriv_weighted (dim := d) d i) x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (norm_nonneg _) _))
  have hCg (j : ℕ) (x : Rd d) (hx : ‖x‖ ≤ 1) :
      ‖iteratedFDeriv ℝ j g x‖ ≤ Cg j :=
    (Classical.choose_spec (symbolAux_iteratedFDeriv_bounded_seed hκ j) x hx).trans
      (le_max_left _ _)
  have hCp0 (i : ℕ) : 0 ≤ Cp i := le_max_right _ _
  have hCg0 (i : ℕ) : 0 ≤ Cg i := le_max_right _ _
  let C : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cp i * Cg (n - i)
  refine ⟨C, fun ζ hζ hζ1 => ?_⟩
  let r : ℝ := ‖ζ‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ 1 := hζ1
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ({0}ᶜ : Set (Rd d)) := by
    intro x hx
    exact ((contDiffAt_norm ℝ (show x ≠ 0 from hx)).pow d).contDiffWithinAt
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ({0}ᶜ : Set (Rd d)) :=
    (symbolAux_contDiff_seed hκ).contDiffOn
  have hs : IsOpen ({0}ᶜ : Set (Rd d)) := isClosed_singleton.isOpen_compl
  have hbound := norm_iteratedFDerivWithin_mul_le hf hg hs.uniqueDiffOn
    (show ζ ∈ ({0}ᶜ : Set (Rd d)) from hζ) (by simp : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  simp only [iteratedFDerivWithin_of_isOpen (s := ({0}ᶜ : Set (Rd d)))
    (f := f) _ hs hζ,
    iteratedFDerivWithin_of_isOpen (s := ({0}ᶜ : Set (Rd d)))
    (f := g) _ hs hζ,
    iteratedFDerivWithin_of_isOpen (s := ({0}ᶜ : Set (Rd d)))
    (f := fun z : Rd d => f z * g z) _ hs hζ] at hbound
  calc
    r ^ n * ‖iteratedFDeriv ℝ n (fun z : Rd d => f z * g z) ζ‖ ≤
        r ^ n * (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ζ‖ *
            ‖iteratedFDeriv ℝ (n - i) g ζ‖) :=
      mul_le_mul_of_nonneg_left hbound (pow_nonneg hr0 _)
    _ = ∑ i ∈ Finset.range (n + 1),
          r ^ n * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ζ‖ *
            ‖iteratedFDeriv ℝ (n - i) g ζ‖) := Finset.mul_sum ..
    _ ≤ C * r ^ d := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hpow : r ^ n = r ^ i * r ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_of_le hin]
      have hp : r ^ i * ‖iteratedFDeriv ℝ i f ζ‖ ≤ Cp i * r ^ d := hCp i ζ hζ
      have hg' : r ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) g ζ‖ ≤ Cg (n - i) := by
        calc
          r ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) g ζ‖ ≤
            1 * ‖iteratedFDeriv ℝ (n - i) g ζ‖ := by
            gcongr
            exact pow_le_one₀ hr0 hr1
          _ ≤ Cg (n - i) := by simpa using hCg (n - i) ζ hζ1
      calc
        r ^ n * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ζ‖ *
            ‖iteratedFDeriv ℝ (n - i) g ζ‖) =
          (n.choose i : ℝ) * (r ^ i * ‖iteratedFDeriv ℝ i f ζ‖) *
            (r ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) g ζ‖) := by
          rw [hpow]
          ring
        _ ≤ (n.choose i : ℝ) * (Cp i * r ^ d) * Cg (n - i) := by
          gcongr
        _ = ((n.choose i : ℝ) * Cp i * Cg (n - i)) * r ^ d := by ring

end ConvKernelNearZero

section ConvKernelDerivativeBounds
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelDerivativeBounds`. -/

open Set
open HigherDimLFPP (Rd)

/-- Sign-free copy of `HigherDimLQGMetric.symbolPerturb_deriv_uniform`. -/
theorem symbolPerturb_deriv_uniform_seed {d : ℕ} {κ : Rd d → ℝ}
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i ≤ n, ∀ ζ : Rd d, ζ ≠ 0 → ‖ζ‖ ≤ 1 →
      ‖ζ‖ ^ i * ‖iteratedFDeriv ℝ i
        (fun z : Rd d => ‖z‖ ^ d * symbolAux κ z) ζ‖ ≤ A * ‖ζ‖ ^ d := by
  have h := finite_uniform_weighted_bound
    (fun (i : ℕ) (ζ : Rd d) => ‖ζ‖ ^ i * ‖iteratedFDeriv ℝ i
      (fun z : Rd d => ‖z‖ ^ d * symbolAux κ z) ζ‖)
    (fun ζ : Rd d => ‖ζ‖ ^ d)
    ({ζ : Rd d | ζ ≠ 0 ∧ ‖ζ‖ ≤ 1})
    (fun ζ _ => pow_nonneg (norm_nonneg _) _)
    (fun i => by
      obtain ⟨C, hC⟩ := symbolPerturb_iteratedFDeriv_weighted_seed hκ i
      exact ⟨C, fun ζ hζ => hC ζ hζ.1 hζ.2⟩) n
  obtain ⟨A, hA, hAi⟩ := h
  exact ⟨A, hA, fun i hi ζ hζ hζ1 => hAi i hi ζ ⟨hζ, hζ1⟩⟩

/-- Sign-free copy of `HigherDimLQGMetric.symbolPerturb_scaled_deriv_bounded`. -/
theorem symbolPerturb_scaled_deriv_bounded_seed {d : ℕ} {κ : Rd d → ℝ}
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i ≤ n, ∀ (r : ℝ) (u : Rd d),
      0 < r → r ≤ 1 → ‖u‖ = 1 →
      ‖iteratedFDeriv ℝ i
        (fun y : Rd d => ‖r • y‖ ^ d * symbolAux κ (r • y)) u‖ ≤ A * r ^ d := by
  obtain ⟨A, hA, hAi⟩ := symbolPerturb_deriv_uniform_seed hκ n
  refine ⟨A, hA, fun i hi r u hr hr1 hu => ?_⟩
  let p : Rd d → ℝ := fun z => ‖z‖ ^ d * symbolAux κ z
  have hru : ‖r • u‖ = r := by simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]
  have hru0 : r • u ≠ 0 := by
    intro he
    have := hru
    simp [he] at this
    linarith
  have hscale := congrFun (iteratedFDeriv_comp_const_smul_any r p i) u
  have hb := hAi i hi (r • u) hru0 (by simpa only [hru] using hr1)
  rw [hru] at hb
  rw [hscale]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _)] using hb

end ConvKernelDerivativeBounds

section ConvKernelNearZeroSqrt
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelNearZeroSqrt`. -/

open Set
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- A2.4 derivative bound at a scaled unit vector.
Sign-free copy of `HigherDimLQGMetric.kernelSymbol_iteratedFDeriv_scaled_near_zero`. -/
theorem kernelSymbol_iteratedFDeriv_scaled_near_zero_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, ∀ (r : ℝ) (u : Rd d), 0 < r → r ≤ 1 → ‖u‖ = 1 →
      |‖r • u‖ ^ d * symbolAux κ (r • u)| ≤ 1 / 2 →
      r ^ n * ‖iteratedFDeriv ℝ n (kernelSymbol κ) (r • u)‖ ≤ C * r ^ d := by
  obtain ⟨A, hA, hAi⟩ := symbolPerturb_scaled_deriv_bounded_seed hκ n
  obtain ⟨B, hB, hBi⟩ := sqrt_one_sub_deriv_bounded n
  let C : ℝ := (n.factorial : ℝ) * B * A ^ n
  refine ⟨C, fun r u hr hr1 hu hp0 => ?_⟩
  let p : Rd d → ℝ := fun z => ‖z‖ ^ d * symbolAux κ z
  let q : Rd d → ℝ := fun y => p (r • y)
  let φ : ℝ → ℝ := fun t => Real.sqrt (1 - t)
  let s : Set (Rd d) := ({0}ᶜ : Set (Rd d)) ∩ q ⁻¹' Iio 1
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hru0 : r • u ≠ 0 := smul_ne_zero hr.ne' hu0
  have hpcont : Continuous p := (continuous_norm.pow d).mul (symbolAux_contDiff_seed hκ).continuous
  have hscaleCont : Continuous (fun y : Rd d => r • y) :=
    (continuous_const : Continuous (fun _ : Rd d => r)).smul continuous_id
  have hqcont : Continuous q := hpcont.comp hscaleCont
  have hsopen : IsOpen s := isClosed_singleton.isOpen_compl.inter (isOpen_Iio.preimage hqcont)
  have huS : u ∈ s := by
    refine ⟨hu0, ?_⟩
    have : |q u| ≤ 1 / 2 := hp0
    have hle : q u ≤ 1 / 2 := le_trans (le_abs_self _) this
    exact lt_of_le_of_lt hle (by norm_num)
  have hpSmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p ({0}ᶜ : Set (Rd d)) := by
    intro z hz
    exact (((contDiffAt_norm ℝ (show z ≠ 0 from hz)).pow d).mul
      (symbolAux_contDiff_seed hκ).contDiffAt).contDiffWithinAt
  have hqSmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q s := by
    intro y hy
    have hy0 : r • y ≠ 0 := smul_ne_zero hr.ne' hy.1
    have hpa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p (r • y) :=
      hpSmooth.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hy0)
    exact (hpa.comp y (contDiff_id.const_smul r).contDiffAt).contDiffWithinAt
  have hmap : MapsTo q s (Iio 1) := fun y hy => hy.2
  let D : ℝ := A * r ^ ((d : ℝ) / (n : ℝ))
  have houter : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i φ (Iio 1) (q u)‖ ≤ B := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Iio huS.2]
    exact hBi i hi (q u) hp0
  have hinner : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i q s u‖ ≤ D ^ i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hsopen huS]
    exact (hAi i hin r u hr hr1 hu).trans
      (scale_factor_bound hn hi hin hA hr hr1)
  have hc := norm_iteratedFDerivWithin_comp_le sqrt_one_sub_contDiffOn hqSmooth
    (by simp : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)) isOpen_Iio.uniqueDiffOn
    hsopen.uniqueDiffOn hmap huS houter hinner
  rw [iteratedFDerivWithin_of_isOpen n hsopen huS] at hc
  have hpow : D ^ n = A ^ n * r ^ d := by
    simp only [D, mul_pow]
    rw [← Real.rpow_mul_natCast (le_of_lt hr)]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have he : (d : ℝ) / (n : ℝ) * (n : ℝ) = d := by field_simp
    rw [he, Real.rpow_natCast]
  rw [hpow] at hc
  have heq : (φ ∘ q) = fun y : Rd d => kernelSymbol κ (r • y) := by
    funext y
    change Real.sqrt (1 - (‖r • y‖ ^ d * symbolAux κ (r • y))) =
      kernelSymbol κ (r • y)
    rw [kernelSymbol_eq_sqrt_symbolSq,
      kernelSymbol_sq_eq_one_sub_pow_aux_seed hd hκ]
  rw [heq] at hc
  have hscale := congrFun (iteratedFDeriv_comp_const_smul_any r (kernelSymbol κ) n) u
  rw [hscale] at hc
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _), C,
    mul_assoc, mul_comm, mul_left_comm] using hc

/-- A2.4 weighted derivative bound on a punctured neighborhood of zero.
Sign-free copy of `HigherDimLQGMetric.kernelSymbol_iteratedFDeriv_near_zero`. -/
theorem kernelSymbol_iteratedFDeriv_near_zero_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) (hn : 0 < n) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ C : ℝ, ∀ ζ : Rd d,
      ζ ≠ 0 → ‖ζ‖ < ρ →
      ‖ζ‖ ^ n * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤ C * ‖ζ‖ ^ d := by
  obtain ⟨ρ, hρ, hρ1, hsmall⟩ := symbolAux_small_near_zero_seed hd hκ
  obtain ⟨C, hC⟩ := kernelSymbol_iteratedFDeriv_scaled_near_zero_seed hd hκ n hn
  refine ⟨ρ, hρ, hρ1, C, fun ζ hζ hζρ => ?_⟩
  let r : ℝ := ‖ζ‖
  have hr : 0 < r := norm_pos_iff.mpr hζ
  let u : Rd d := r⁻¹ • ζ
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, r, inv_mul_cancel₀ hr.ne']
  have hru : r • u = ζ := by simp [u, smul_smul, mul_inv_cancel₀ hr.ne']
  have hp0 : |‖r • u‖ ^ d * symbolAux κ (r • u)| ≤ 1 / 2 := by
    rw [hru]
    exact hsmall ζ hζρ
  have h := hC r u hr (le_trans (le_of_lt hζρ) hρ1) hu hp0
  rw [hru] at h
  exact h

end ConvKernelNearZeroSqrt

section ConvKernelNearIntegrable
/-! Copies from `HigherDimLQGMetric.Kernel.ConvKernelNearIntegrable`. -/

open MeasureTheory Set
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Each positive-order symbol derivative of order less than `2d` is integrable near zero.
Sign-free copy of `HigherDimLQGMetric.integrableOn_kernelSymbol_iteratedFDeriv_near_zero`. -/
theorem integrableOn_kernelSymbol_iteratedFDeriv_near_zero_seed (hd : 0 < d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) (hn : 0 < n)
    (hnd : n < 2 * d) :
    ∃ ρ : ℝ, 0 < ρ ∧
      IntegrableOn (iteratedFDeriv ℝ n (kernelSymbol κ))
        (Metric.ball (0 : Rd d) ρ) := by
  obtain ⟨ρ, hρ, hρ1, C, hC⟩ := kernelSymbol_iteratedFDeriv_near_zero_seed hd hκ n hn
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
      (kernelSymbol_contDiffOn_seed hd hκ) (isClosed_singleton.isOpen_compl) (by simp)
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

end ConvKernelNearIntegrable

end HigherDimLFPPAS.Signed
