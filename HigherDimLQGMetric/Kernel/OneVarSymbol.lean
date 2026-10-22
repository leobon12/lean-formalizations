import HigherDimLQGMetric.Frozen.KernelSymbol
import HigherDimLQGMetric.Kernel.OneVarFourier
import HigherDimLQGMetric.Kernel.OneVarTail

/-!
# The symbol tail `G = symbolSq κ`: `G(0) = 1` and `G > 0` (target `L1a_symbolSq`)

Packet L1b (block B1). Source: audit MA5 Details (a) A2.1 (`G(0) = 1`: Plancherel and polar
coordinates) and A2.3 (`G > 0`: a band-limited function with compact support vanishes), Details (c)
(the definitions `symbolSq`, `L1a_symbolSq`, copied verbatim); [1] = arXiv 2512.06292, Remark 1.1,
Lemma 2.10.

`symbolSq κ ρ = |S^{d-1}| ∫_ρ^∞ t^{d-1} |𝓕κ(t e₁)|² dt` with `|S^{d-1}| = 2π^{d/2}/Γ(d/2)`, so that the
frozen `kernelSymbol κ ζ = √(symbolSq κ ‖ζ‖)` (`kernelSymbol_eq_sqrt_symbolSq`, by `rfl`).

* `symbolSq_zero` — `G(0) = ∫ |𝓕κ|² = ∫ κ² = 1`.
* `integral_symbolIntegrand_pos`, `symbolSq_pos_of_nonneg` — for `ρ ≥ 0`: if `G(ρ) = 0`, the continuous
  nonnegative integrand vanishes on `(ρ, ∞)`, so (radiality) `𝓕κ = 0` off `B̄(0, ρ)`, hence `𝓕κ ≡ 0`
  (`fourier_eq_zero_of_far`), contradicting Plancherel.
* `symbolSq_pos` — all `ρ : ℝ`. For `ρ < 0` (the statement quantifies over all real `ρ`, a case MA5
  does not discuss): if `d - 1` is even the integrand is `≥ 0` on `ℝ` and `G(ρ) ≥ G(0) = 1`; if `d - 1`
  is odd the integrand is odd and `G(ρ) = G(-ρ) > 0`.
* `L1a_symbolSq`, `l1a_symbolSq` — the target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- `G(ρ) = |S^{d-1}| ∫_ρ^∞ t^{d-1} |𝔎̂(t e₁)|² dt`; `kernelSymbol κ ζ = √(G(‖ζ‖))` ([1] Rem. 1.1). -/
def symbolSq (κ : Rd d → ℝ) (ρ : ℝ) : ℝ :=
  (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
    ∫ t in Ioi ρ, t ^ (d - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e₁ d)‖ ^ 2

lemma kernelSymbol_eq_sqrt_symbolSq (κ : Rd d → ℝ) (ζ : Rd d) :
    kernelSymbol κ ζ = Real.sqrt (symbolSq κ ‖ζ‖) := rfl

/-- The integrand `t ↦ t^{d-1} |𝓕κ(t e₁)|²` of `symbolSq`. -/
def symbolIntegrand (κ : Rd d → ℝ) (t : ℝ) : ℝ :=
  t ^ (d - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e₁ d)‖ ^ 2

lemma symbolSq_eq (κ : Rd d → ℝ) (ρ : ℝ) :
    symbolSq κ ρ = (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
      ∫ t in Ioi ρ, symbolIntegrand κ t := rfl

/-- `|S^{d-1}| = 2π^{d/2}/Γ(d/2) > 0`. -/
lemma sphereConst_pos (hd : 0 < d) :
    0 < 2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2) := by
  have hd' : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have := Real.Gamma_pos_of_pos hd'
  have := Real.rpow_pos_of_pos Real.pi_pos ((d : ℝ) / 2)
  positivity

section Kernel

variable {κ : Rd d → ℝ}

theorem continuous_symbolIntegrand (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Continuous (symbolIntegrand κ) := by
  have hF := continuous_fourier_kernel hκ
  unfold symbolIntegrand
  fun_prop

theorem symbolIntegrand_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ symbolIntegrand κ t := by
  unfold symbolIntegrand
  positivity

theorem symbolIntegrand_nonneg_of_even (hev : Even (d - 1)) (t : ℝ) :
    0 ≤ symbolIntegrand κ t := by
  unfold symbolIntegrand
  exact mul_nonneg (hev.pow_nonneg t) (sq_nonneg _)

theorem symbolIntegrand_neg_of_odd (hrad : ∀ z w : Rd d, ‖z‖ = ‖w‖ → κ z = κ w)
    (hodd : Odd (d - 1)) (t : ℝ) : symbolIntegrand κ (-t) = -symbolIntegrand κ t := by
  unfold symbolIntegrand
  rw [hodd.neg_pow, fourier_kernel_eq_of_norm_eq hrad (ζ' := t • e₁ d) (by
    rw [norm_smul, norm_smul, norm_neg])]
  ring

/-- Decay of the integrand: `s² |φ(s)| ≤ C` for `s ≥ 1`. -/
theorem symbolIntegrand_decay (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ C : ℝ, ∀ s, 1 ≤ s → s ^ 2 * |symbolIntegrand κ s| ≤ C := by
  obtain ⟨C₀, _, hC₀⟩ := fourier_kernel_decay hκ 0
  obtain ⟨C₁, _, hC₁⟩ := fourier_kernel_decay hκ (d + 1)
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

theorem integrableOn_symbolIntegrand (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) (a : ℝ) :
    IntegrableOn (symbolIntegrand κ) (Ioi a) := by
  obtain ⟨C, hC⟩ := symbolIntegrand_decay hd hκ
  exact integrableOn_Ioi_of_decay (continuous_symbolIntegrand hκ) hC a

/-- **`G(0) = 1`** (MA5 A2.1): polar coordinates and Plancherel. -/
theorem symbolSq_zero (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) : symbolSq κ 0 = 1 := by
  rw [← integral_norm_sq_fourier_kernel hκ, integral_norm_sq_fourier_kernel_polar hd hκ.radial]
  rfl

/-- **`G(ρ) > 0` for `ρ ≥ 0`** (MA5 A2.3), integral form. -/
theorem integral_symbolIntegrand_pos (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : 0 < ∫ t in Ioi ρ, symbolIntegrand κ t := by
  have hint := integrableOn_symbolIntegrand hd hκ ρ
  have hnn : ∀ t ∈ Ioi ρ, 0 ≤ symbolIntegrand κ t := fun t ht =>
    symbolIntegrand_nonneg (hρ.trans (le_of_lt ht))
  rcases (setIntegral_nonneg measurableSet_Ioi hnn).eq_or_lt with h0 | hpos
  · exfalso
    have hae : symbolIntegrand κ =ᵐ[volume.restrict (Ioi ρ)] 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae
        ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hnn)) hint).1 h0.symm
    have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
      (continuous_symbolIntegrand hκ).continuousOn continuousOn_const
    have hfar : ∀ ζ : Rd d, ρ < ‖ζ‖ → 𝓕 (fun x : Rd d => (κ x : ℂ)) ζ = 0 := by
      intro ζ hζ
      have h1 : symbolIntegrand κ ‖ζ‖ = 0 := heq hζ
      unfold symbolIntegrand at h1
      have hpow : ‖ζ‖ ^ (d - 1) ≠ 0 := pow_ne_zero _ (by linarith)
      have h2 := (mul_eq_zero.1 h1).resolve_left hpow
      rw [fourier_kernel_eq_norm_smul_e₁ hd hκ.radial ζ]
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
    have hall := fourier_eq_zero_of_far hd (contDiff_ofReal_kernel hκ).continuous
      (hasCompactSupport_ofReal_kernel hκ) hfar
    have h1 := integral_norm_sq_fourier_kernel hκ
    simp only [hall, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero] at h1
    exact zero_ne_one h1
  · exact hpos

theorem symbolSq_pos_of_nonneg (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : 0 < symbolSq κ ρ :=
  mul_pos (sphereConst_pos hd) (integral_symbolIntegrand_pos hd hκ hρ)

/-- **`G(ρ) > 0` for every real `ρ`.** -/
theorem symbolSq_pos (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ρ : ℝ) :
    0 < symbolSq κ ρ := by
  rcases le_or_gt 0 ρ with hρ | hρ
  · exact symbolSq_pos_of_nonneg hd hκ hρ
  rw [symbolSq_eq]
  refine mul_pos (sphereConst_pos hd) ?_
  have hint := integrableOn_symbolIntegrand hd hκ
  have hsplit := intervalIntegral.integral_interval_add_Ioi (hint ρ) (hint 0)
  have hpos0 := integral_symbolIntegrand_pos hd hκ (le_refl 0)
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
    have hposρ := integral_symbolIntegrand_pos hd hκ (le_of_lt (neg_pos.2 hρ))
    linarith

end Kernel

/-- **L1a** (G > 0; needed for smoothness of `K̂` off `0`; MA5 Details (c), verbatim): `G(0) = 1` and
`G(ρ) > 0` for all `ρ`. Proof: Plancherel and polar coordinates for `G(0)`; for positivity, a nonzero
compactly supported `𝔎` cannot have compactly supported `𝔎̂` (MA5 Details (a) A2.3; here via
analyticity of `t ↦ 𝔎̂(ζ + t e₁)`, `fourier_eq_zero_of_far`). -/
def L1a_symbolSq : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
    symbolSq κ 0 = 1 ∧ ∀ ρ : ℝ, 0 < symbolSq κ ρ

/-- **Target `L1a_symbolSq`** (packet L1b). -/
theorem l1a_symbolSq : L1a_symbolSq := fun _ hd _ hκ =>
  ⟨symbolSq_zero (by omega) hκ, symbolSq_pos (by omega) hκ⟩

end HigherDimLQGMetric
