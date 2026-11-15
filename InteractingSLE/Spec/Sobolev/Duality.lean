import InteractingSLE.Spec.Sobolev.GFFRegularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion

/-!
# Duality between `H^{-ε}` and `H^ε` for compactly supported distributions

Source: `source/spec/p049-096.md`, proof of Aux. lemma 12 (`#aux-12-proof`, p. 85: "The first bound
uses a fixed compact cutoff of `T` belonging to `H^{-ε}`": `|T(φ v_δ)| ≤ C ‖φ v_δ‖_{H^ε}`).

For a smooth compactly supported `ψ : ℂ → ℝ` write `a(ξ) = ∫ ψ cos(2π⟪·,ξ⟫)` and
`b(ξ) = ∫ ψ sin(2π⟪·,ξ⟫)`, so that `𝓕ψ = a - i b`, and
`‖ψ‖²_{H^ε} = ∫ (a² + b²)(1 + |ξ|²)^ε dξ` (`sobolevSq`). Fourier inversion reads
`ψ(x) = ∫ (a(ξ) cos(2π⟪x,ξ⟫) + b(ξ) sin(2π⟪x,ξ⟫)) dξ`, and the interchange
`apply_integral_kernel` gives, for a distribution `T` and a cutoff `ζ`,

  `T(ζψ) = ∫ a(ξ) T(ζ cos(2π⟪·,ξ⟫)) dξ + ∫ b(ξ) T(ζ sin(2π⟪·,ξ⟫)) dξ`,

whence, by Cauchy–Schwarz, `T(ζψ)² ≤ 4 ‖ζT‖²_{H^{-ε}} ‖ψ‖²_{H^ε}`.

## Main results

* `fourierCos`, `fourierSin`, `sobolevSq` : the real Fourier coefficients and the `H^s` norm;
* `fourier_inversion_trig` : Fourier inversion in cos/sin form;
* `apply_mulTest_eq` : the pairing `T(ζψ)` as an integral over frequencies;
* `sq_apply_mulTest_le` : `T(ζψ)² ≤ 4 ‖ζT‖²_{H^{-ε}} ‖ψ‖²_{H^ε}`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function Real FourierTransform
open scoped Distributions ContDiff ENNReal RealInnerProductSpace SchwartzMap

namespace InteractingSLE.Sobolev

open LQGMetric TopologicalSpace

/-! ### Real Fourier coefficients -/

/-- The complexification of a real function. -/
def cplx (ψ : ℂ → ℝ) (x : ℂ) : ℂ := (ψ x : ℂ)

/-- `a(ξ) = Re 𝓕ψ(ξ) = ∫ ψ(x) cos(2π⟪x, ξ⟫) dx` (Mathlib's `𝓕 f ξ = ∫ e^{-2πi⟪x,ξ⟫} f x dx`). -/
def fourierCos (ψ : ℂ → ℝ) (ξ : ℂ) : ℝ := (𝓕 (cplx ψ) ξ).re

/-- `b(ξ) = -Im 𝓕ψ(ξ) = ∫ ψ(x) sin(2π⟪x, ξ⟫) dx`. -/
def fourierSin (ψ : ℂ → ℝ) (ξ : ℂ) : ℝ := -(𝓕 (cplx ψ) ξ).im

/-- `‖ψ‖²_{H^s(ℝ²)} = ∫ |𝓕ψ(ξ)|² (1 + |ξ|²)^s dξ` (the Fourier definition). -/
def sobolevSq (s : ℝ) (ψ : ℂ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (‖𝓕 (cplx ψ) ξ‖ ^ 2 * sobWeight s ξ)

theorem fourierCos_sq_add_fourierSin_sq (ψ : ℂ → ℝ) (ξ : ℂ) :
    fourierCos ψ ξ ^ 2 + fourierSin ψ ξ ^ 2 = ‖𝓕 (cplx ψ) ξ‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, fourierCos, fourierSin]
  ring

theorem re_fourierChar_smul (t : ℝ) (z : ℂ) :
    (𝐞 t • z).re = Real.cos (2 * π * t) * z.re - Real.sin (2 * π * t) * z.im := by
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- `(1 + r)^m ≤ 2^m (1 + r^m)` for `r ≥ 0`. -/
theorem one_add_pow_le (m : ℕ) {r : ℝ} (hr : 0 ≤ r) : (1 + r) ^ m ≤ 2 ^ m * (1 + r ^ m) := by
  rcases le_total r 1 with h | h
  · calc (1 + r) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + r ^ m) := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (by positivity))
  · calc (1 + r) ^ m ≤ (2 * r) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * r ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + r ^ m) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

section Coefficients

variable {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
include hψ hψc

omit hψc in
theorem contDiff_cplx : ContDiff ℝ ∞ (cplx ψ) := Complex.ofRealCLM.contDiff.comp hψ

omit hψ in
theorem hasCompactSupport_cplx : HasCompactSupport (cplx ψ) :=
  hψc.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero

/-- The Schwartz function `ψ : ℂ → ℂ`. -/
def schwartzCplx : 𝓢(ℂ, ℂ) :=
  (hasCompactSupport_cplx hψc).toSchwartzMap (contDiff_cplx hψ)

theorem coe_schwartzCplx : ⇑(schwartzCplx hψ hψc) = cplx ψ := rfl

theorem fourier_cplx_eq : 𝓕 (cplx ψ) = ⇑(𝓕 (schwartzCplx hψ hψc) : 𝓢(ℂ, ℂ)) := by
  rw [SchwartzMap.fourier_coe, coe_schwartzCplx]

theorem integrable_fourier_cplx : Integrable (𝓕 (cplx ψ)) := by
  rw [fourier_cplx_eq hψ hψc]
  exact (𝓕 (schwartzCplx hψ hψc) : 𝓢(ℂ, ℂ)).integrable

theorem continuous_fourier_cplx : Continuous (𝓕 (cplx ψ)) := by
  rw [fourier_cplx_eq hψ hψc]
  exact (𝓕 (schwartzCplx hψ hψc) : 𝓢(ℂ, ℂ)).continuous

/-- The Fourier transform of a test function is integrable against every polynomial weight. -/
theorem integrable_one_add_pow_mul_norm_fourier (m : ℕ) :
    Integrable (fun ξ => (1 + ‖ξ‖) ^ m * ‖𝓕 (cplx ψ) ξ‖) := by
  rw [fourier_cplx_eq hψ hψc]
  set f : 𝓢(ℂ, ℂ) := 𝓕 (schwartzCplx hψ hψc)
  have h1 : Integrable (fun ξ => 2 ^ m * (‖f ξ‖ + ‖ξ‖ ^ m * ‖f ξ‖)) :=
    (f.integrable.norm.add (f.integrable_pow_mul volume m)).const_mul _
  refine h1.mono' ((continuous_const.add continuous_norm).pow m |>.mul
    f.continuous.norm).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (1 + ‖ξ‖) ^ m * ‖f ξ‖ ≤ 2 ^ m * (1 + ‖ξ‖ ^ m) * ‖f ξ‖ :=
        mul_le_mul_of_nonneg_right (one_add_pow_le m (norm_nonneg _)) (norm_nonneg _)
    _ = 2 ^ m * (‖f ξ‖ + ‖ξ‖ ^ m * ‖f ξ‖) := by ring

theorem integrable_pow_mul_fourierCos (m : ℕ) :
    Integrable (fun ξ => (1 + ‖ξ‖) ^ m * fourierCos ψ ξ) := by
  refine (integrable_one_add_pow_mul_norm_fourier hψ hψc m).mono'
    (((continuous_const.add continuous_norm).pow m).mul
      (Complex.continuous_re.comp (continuous_fourier_cplx hψ hψc))).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, Real.norm_eq_abs (fourierCos ψ ξ), Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)

theorem integrable_pow_mul_fourierSin (m : ℕ) :
    Integrable (fun ξ => (1 + ‖ξ‖) ^ m * fourierSin ψ ξ) := by
  refine (integrable_one_add_pow_mul_norm_fourier hψ hψc m).mono'
    (((continuous_const.add continuous_norm).pow m).mul
      (Complex.continuous_im.comp (continuous_fourier_cplx hψ hψc)).neg).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, Real.norm_eq_abs (fourierSin ψ ξ), Real.norm_eq_abs, abs_of_nonneg (by positivity),
    fourierSin, abs_neg]
  exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by positivity)

/-- **Fourier inversion** in cos/sin form. -/
theorem fourier_inversion_trig (x : ℂ) :
    ψ x = ∫ ξ, (fourierCos ψ ξ * Real.cos (2 * π * ⟪x, ξ⟫) +
      fourierSin ψ ξ * Real.sin (2 * π * ⟪x, ξ⟫)) := by
  have hc : Continuous (cplx ψ) := (contDiff_cplx hψ).continuous
  have hi : Integrable (cplx ψ) := hc.integrable_of_hasCompactSupport (hasCompactSupport_cplx hψc)
  have hinv := hc.fourierInv_fourier_eq hi (integrable_fourier_cplx hψ hψc)
  have hx : ψ x = (cplx ψ x).re := by simp [cplx]
  rw [hx, ← hinv, Real.fourierInv_eq]
  have hint : Integrable (fun ξ => 𝐞 (⟪ξ, x⟫) • 𝓕 (cplx ψ) ξ) := by
    refine (integrable_fourier_cplx hψ hψc).norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        (continuous_fourier_cplx hψ hψc)).aestronglyMeasurable
    · rw [Circle.norm_smul]
  refine (integral_re hint).symm.trans ?_
  congr 1
  funext ξ
  change (𝐞 ⟪ξ, x⟫ • 𝓕 (cplx ψ) ξ).re = _
  rw [re_fourierChar_smul, real_inner_comm, fourierCos, fourierSin]
  ring

end Coefficients

/-! ### The pairing `T(ζψ)` as an integral over frequencies -/

section Pairing

variable {U : Opens ℂ}

/-- `ζψ` as a test function on `U` (`ζ ∈ 𝓓(U)`, `ψ` smooth on `ℂ`). -/
def mulTest (ζ : TestOn U) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) : TestOn U :=
  ⟨fun x => ζ x * ψ x, ζ.contDiff.mul hψ, ζ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans ζ.tsupport_subset⟩

@[simp] theorem mulTest_apply (ζ : TestOn U) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : ℂ) :
    mulTest ζ hψ x = ζ x * ψ x := rfl

/-- The test function `x ↦ ∫ g ξ * k ξ x dξ` for a kernel supported in `tsupport ζ`. -/
def kernelIntegralTest (ζ : TestOn U) {k : ℂ → ℂ → ℝ} (hk : ContDiff ℝ ∞ (uncurry k))
    (hkK : ∀ ξ x, x ∉ tsupportCompact ζ → k ξ x = 0)
    (hbd : ∀ i : ℕ, ∃ C, ∀ ξ x, ‖iteratedFDeriv ℝ i (k ξ) x‖ ≤ C * (1 + ‖ξ‖) ^ i)
    {g : ℂ → ℝ} (hg : ∀ m : ℕ, Integrable (fun ξ => (1 + ‖ξ‖) ^ m * g ξ)) : TestOn U :=
  have hsupp : support (fun x => ∫ ξ, g ξ * k ξ x) ⊆ tsupport ζ := fun x hx => by
    by_contra h
    exact hx (by simp [hkK _ x h])
  ⟨fun x => ∫ ξ, g ξ * k ξ x, contDiff_integral_kernel hk hbd hg,
    IsCompact.of_isClosed_subset ζ.hasCompactSupport (isClosed_tsupport _)
      (closure_minimal hsupp (isClosed_tsupport _)),
    (closure_minimal hsupp (isClosed_tsupport _)).trans ζ.tsupport_subset⟩

theorem integrable_mul_trig {g : ℂ → ℝ} (hg : Integrable g) (hgc : Continuous g) (c : ℝ)
    {t : ℝ → ℝ} (ht : Continuous t) (htb : ∀ s, |t s| ≤ 1) (x : ℂ) :
    Integrable (fun ξ => g ξ * (c * t (2 * π * ⟪x, ξ⟫))) := by
  refine (hg.norm.const_mul |c|).mono' (hgc.mul (continuous_const.mul (ht.comp
    (continuous_const.mul (continuous_const.inner continuous_id))))).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, norm_mul, Real.norm_eq_abs c, Real.norm_eq_abs (t _)]
  calc ‖g ξ‖ * (|c| * |t (2 * π * ⟪x, ξ⟫)|) ≤ ‖g ξ‖ * (|c| * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (htb _) (abs_nonneg _))
          (norm_nonneg _)
    _ = |c| * ‖g ξ‖ := by ring

/-- `T(ζψ) = ∫ a(ξ) T(ζ cos(2π⟪·,ξ⟫)) dξ + ∫ b(ξ) T(ζ sin(2π⟪·,ξ⟫)) dξ`. -/
theorem apply_mulTest_eq (T : DistOn U) (ζ : TestOn U) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    T (mulTest ζ hψ) =
      (∫ ξ, fourierCos ψ ξ * T (cosTest ζ ξ)) + ∫ ξ, fourierSin ψ ξ * T (sinTest ζ ξ) := by
  have hc := integrable_pow_mul_fourierCos hψ hψc
  have hs := integrable_pow_mul_fourierSin hψ hψc
  have hcos := fun i => cosKer_bound ζ.contDiff ζ.hasCompactSupport i
  have hsin := fun i => sinKer_bound ζ.contDiff ζ.hasCompactSupport i
  set Fc := kernelIntegralTest ζ (contDiff_cosKer ζ.contDiff) (cosKer_eq_zero ζ) hcos hc
  set Fs := kernelIntegralTest ζ (contDiff_sinKer ζ.contDiff) (sinKer_eq_zero ζ) hsin hs
  have hTc : T Fc = ∫ ξ, fourierCos ψ ξ * T (cosTest ζ ξ) :=
    apply_integral_kernel T (tsupportCompact_subset ζ) (contDiff_cosKer ζ.contDiff)
      (cosKer_eq_zero ζ) hcos hc Fc (fun x => rfl)
  have hTs : T Fs = ∫ ξ, fourierSin ψ ξ * T (sinTest ζ ξ) :=
    apply_integral_kernel T (tsupportCompact_subset ζ) (contDiff_sinKer ζ.contDiff)
      (sinKer_eq_zero ζ) hsin hs Fs (fun x => rfl)
  have hci : Integrable (fourierCos ψ) := by simpa using hc 0
  have hsi : Integrable (fourierSin ψ) := by simpa using hs 0
  have hcc : Continuous (fourierCos ψ) := Complex.continuous_re.comp (continuous_fourier_cplx hψ hψc)
  have hsc : Continuous (fourierSin ψ) :=
    (Complex.continuous_im.comp (continuous_fourier_cplx hψ hψc)).neg
  have heq : mulTest ζ hψ = Fc + Fs := by
    refine TestFunction.ext fun x => ?_
    change ζ x * ψ x = (∫ ξ, fourierCos ψ ξ * cosKer ζ ξ x) + ∫ ξ, fourierSin ψ ξ * sinKer ζ ξ x
    simp only [cosKer, sinKer]
    rw [fourier_inversion_trig hψ hψc x, ← integral_const_mul,
      ← integral_add (integrable_mul_trig hci hcc (ζ x) Real.continuous_cos Real.abs_cos_le_one x)
        (integrable_mul_trig hsi hsc (ζ x) Real.continuous_sin Real.abs_sin_le_one x)]
    congr 1
    funext ξ
    ring
  rw [heq, map_add, hTc, hTs]

/-- Squared Cauchy–Schwarz for lower integrals. -/
theorem sq_lintegral_mul_le {f g : ℂ → ℝ≥0∞} (hf : AEMeasurable f) (hg : AEMeasurable g) :
    (∫⁻ x, f x * g x) ^ 2 ≤ (∫⁻ x, f x ^ 2) * ∫⁻ x, g x ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hf hg
  have e : ∀ y : ℝ≥0∞, y ^ (2 : ℝ) = y ^ 2 := fun y => by
    rw [← ENNReal.rpow_natCast]; norm_num
  simp only [e, Pi.mul_apply] at h
  calc (∫⁻ x, f x * g x) ^ 2
      ≤ ((∫⁻ x, f x ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ x, g x ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ = (∫⁻ x, f x ^ 2) * ∫⁻ x, g x ^ 2 := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

/-- One half of the duality bound: `(∫ a T(ζ t(2π⟪·,ξ⟫)))² ≤ ‖ζT‖²_{H^{-ε}} ‖ψ‖²_{H^ε}`. -/
theorem ofReal_sq_integral_le {a c : ℂ → ℝ} (hac : Continuous a) (hcc : Continuous c) {N S : ℝ≥0∞}
    (ε : ℝ) (hN : ∫⁻ ξ, ENNReal.ofReal (c ξ ^ 2 * sobWeight (-ε) ξ) ≤ N)
    (hS : ∫⁻ ξ, ENNReal.ofReal (a ξ ^ 2 * sobWeight ε ξ) ≤ S) :
    ENNReal.ofReal ((∫ ξ, a ξ * c ξ) ^ 2) ≤ N * S := by
  set F : ℂ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (|a ξ| * √(sobWeight ε ξ))
  set G : ℂ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (|c ξ| * √(sobWeight (-ε) ξ))
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    ((hac.abs.mul ((continuous_sobWeight ε).sqrt)).measurable)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp
    ((hcc.abs.mul ((continuous_sobWeight (-ε)).sqrt)).measurable)
  have hw : ∀ ξ, √(sobWeight ε ξ) * √(sobWeight (-ε) ξ) = 1 := fun ξ => by
    rw [← Real.sqrt_mul (sobWeight_pos ε ξ).le, sobWeight, sobWeight,
      Real.rpow_neg (by positivity), mul_inv_cancel₀ (Real.rpow_pos_of_pos (by positivity) ε).ne',
      Real.sqrt_one]
  have hFG : ∀ ξ, ‖a ξ * c ξ‖ₑ = F ξ * G ξ := fun ξ => by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc |a ξ * c ξ| = |a ξ| * |c ξ| * (√(sobWeight ε ξ) * √(sobWeight (-ε) ξ)) := by
          rw [hw, mul_one, abs_mul]
      _ = _ := by ring
  have hF2 : ∀ ξ, F ξ ^ 2 = ENNReal.ofReal (a ξ ^ 2 * sobWeight ε ξ) := fun ξ => by
    rw [← ENNReal.ofReal_pow (by positivity), mul_pow, sq_abs,
      Real.sq_sqrt (sobWeight_pos ε ξ).le]
  have hG2 : ∀ ξ, G ξ ^ 2 = ENNReal.ofReal (c ξ ^ 2 * sobWeight (-ε) ξ) := fun ξ => by
    rw [← ENNReal.ofReal_pow (by positivity), mul_pow, sq_abs,
      Real.sq_sqrt (sobWeight_pos (-ε) ξ).le]
  have h1 : ENNReal.ofReal ((∫ ξ, a ξ * c ξ) ^ 2) = ‖∫ ξ, a ξ * c ξ‖ₑ ^ 2 := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [h1]
  calc ‖∫ ξ, a ξ * c ξ‖ₑ ^ 2 ≤ (∫⁻ ξ, ‖a ξ * c ξ‖ₑ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (enorm_integral_le_lintegral_enorm _) 2
    _ = (∫⁻ ξ, F ξ * G ξ) ^ 2 := by simp_rw [hFG]
    _ ≤ (∫⁻ ξ, F ξ ^ 2) * ∫⁻ ξ, G ξ ^ 2 := sq_lintegral_mul_le hF.aemeasurable hG.aemeasurable
    _ ≤ S * N := by
        simp_rw [hF2, hG2]
        exact mul_le_mul' hS hN
    _ = N * S := mul_comm _ _

/-- **Duality**: `T(ζψ)² ≤ 4 ‖ζT‖²_{H^{-ε}} ‖ψ‖²_{H^ε}`. -/
theorem sq_apply_mulTest_le (T : DistOn U) (ζ : TestOn U) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (ε : ℝ) :
    ENNReal.ofReal (T (mulTest ζ hψ) ^ 2) ≤ 4 * negSobolevSq ε T ζ * sobolevSq ε ψ := by
  rw [apply_mulTest_eq T ζ hψ hψc]
  set Ic := ∫ ξ, fourierCos ψ ξ * T (cosTest ζ ξ)
  set Is := ∫ ξ, fourierSin ψ ξ * T (sinTest ζ ξ)
  have hcc : Continuous (fourierCos ψ) := Complex.continuous_re.comp (continuous_fourier_cplx hψ hψc)
  have hsc : Continuous (fourierSin ψ) :=
    (Complex.continuous_im.comp (continuous_fourier_cplx hψ hψc)).neg
  have hS1 : ∫⁻ ξ, ENNReal.ofReal (fourierCos ψ ξ ^ 2 * sobWeight ε ξ) ≤ sobolevSq ε ψ := by
    refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
      (sobWeight_pos _ _).le)
    rw [← fourierCos_sq_add_fourierSin_sq]
    nlinarith [sq_nonneg (fourierSin ψ ξ)]
  have hS2 : ∫⁻ ξ, ENNReal.ofReal (fourierSin ψ ξ ^ 2 * sobWeight ε ξ) ≤ sobolevSq ε ψ := by
    refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
      (sobWeight_pos _ _).le)
    rw [← fourierCos_sq_add_fourierSin_sq]
    nlinarith [sq_nonneg (fourierCos ψ ξ)]
  have hN1 : ∫⁻ ξ, ENNReal.ofReal (T (cosTest ζ ξ) ^ 2 * sobWeight (-ε) ξ) ≤
      negSobolevSq ε T ζ := by
    refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
      (sobWeight_pos _ _).le)
    simp only [fourierSq]
    nlinarith [sq_nonneg (T (sinTest ζ ξ))]
  have hN2 : ∫⁻ ξ, ENNReal.ofReal (T (sinTest ζ ξ) ^ 2 * sobWeight (-ε) ξ) ≤
      negSobolevSq ε T ζ := by
    refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
      (sobWeight_pos _ _).le)
    simp only [fourierSq]
    nlinarith [sq_nonneg (T (cosTest ζ ξ))]
  have h1 := ofReal_sq_integral_le hcc (T.continuous.comp (continuous_cosTest ζ)) ε hN1 hS1
  have h2 := ofReal_sq_integral_le hsc (T.continuous.comp (continuous_sinTest ζ)) ε hN2 hS2
  calc ENNReal.ofReal ((Ic + Is) ^ 2) ≤ ENNReal.ofReal (2 * Ic ^ 2 + 2 * Is ^ 2) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (Ic - Is)])
    _ = 2 * ENNReal.ofReal (Ic ^ 2) + 2 * ENNReal.ofReal (Is ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ 2 * (negSobolevSq ε T ζ * sobolevSq ε ψ) + 2 * (negSobolevSq ε T ζ * sobolevSq ε ψ) :=
        add_le_add (by gcongr; exact h1) (by gcongr; exact h2)
    _ = 4 * negSobolevSq ε T ζ * sobolevSq ε ψ := by ring

end Pairing

end InteractingSLE.Sobolev
