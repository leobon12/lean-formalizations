/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Smooth cutoffs near finitely many points of the unit circle

Packet PROVE-SEC6-A (specification §6.1, proof of Aux. lemma 28, `source/spec/p145-192.md`,
`#aux-28-proof`, p. 163: "On every compact subarc outside `E` the convergence to zero is
uniform, so `T` is supported on `E`"). The localization of the boundary distribution to the
exceptional set uses cutoffs in the angle variable `t`:

  `χ_δ(t) = ∏_{p ∈ E} η(‖e^{it} − p‖² / δ²)`,

where `η` is smooth, `η = 0` on `(−∞, 1]` and `η = 1` on `[4, ∞)`. Thus `χ_δ(t) = 0` when
`e^{it}` is within `δ` of `E`, `χ_δ(t) = 1` when it is at distance `≥ 2δ` from `E`, and
`|χ_δ'(t)| ≲ 1/δ` with the derivative supported where some `‖e^{it} − p‖ ≤ 2δ`.

## Main definitions

* `cutProfile`: the profile `η`;
* `sqDist p t = ‖e^{it} − p‖²` (`sqDist_eq`), with derivative `sqDistDeriv`;
* `circCutoff E δ`, with derivative `circCutoffDeriv E δ`.
-/

noncomputable section

open Complex Real Filter Topology Set
open scoped Real ComplexConjugate

namespace InteractingSLE.Sec6

/-! ## The profile -/

/-- The cutoff profile `η(s) = smoothTransition((s − 1)/3)`: `0` for `s ≤ 1`, `1` for `s ≥ 4`. -/
def cutProfile (s : ℝ) : ℝ := Real.smoothTransition ((s - 1) / 3)

theorem cutProfile_eq_zero {s : ℝ} (hs : s ≤ 1) : cutProfile s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))

theorem cutProfile_eq_one {s : ℝ} (hs : 4 ≤ s) : cutProfile s = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)

theorem cutProfile_nonneg (s : ℝ) : 0 ≤ cutProfile s := Real.smoothTransition.nonneg _

theorem cutProfile_le_one (s : ℝ) : cutProfile s ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_cutProfile : ContDiff ℝ 1 cutProfile :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem hasDerivAt_cutProfile (s : ℝ) : HasDerivAt cutProfile (deriv cutProfile s) s :=
  ((contDiff_cutProfile.differentiable one_ne_zero) s).hasDerivAt

theorem continuous_deriv_cutProfile : Continuous (deriv cutProfile) :=
  contDiff_cutProfile.continuous_deriv le_rfl

theorem deriv_cutProfile_eq_zero_of_lt {s : ℝ} (hs : s < 1) : deriv cutProfile s = 0 := by
  have h : cutProfile =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hs] with x hx using cutProfile_eq_zero (le_of_lt hx)
  rw [h.deriv_eq, deriv_const]

theorem deriv_cutProfile_eq_zero_of_gt {s : ℝ} (hs : 4 < s) : deriv cutProfile s = 0 := by
  have h : cutProfile =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx using cutProfile_eq_one (le_of_lt hx)
  rw [h.deriv_eq, deriv_const]

theorem exists_bound_deriv_cutProfile : ∃ D, 0 ≤ D ∧ ∀ s, |deriv cutProfile s| ≤ D := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (1 : ℝ) 4)
    continuous_deriv_cutProfile.continuousOn
  refine ⟨max D 0, le_max_right _ _, fun s => ?_⟩
  by_cases h1 : s < 1
  · rw [deriv_cutProfile_eq_zero_of_lt h1, abs_zero]; exact le_max_right _ _
  by_cases h4 : 4 < s
  · rw [deriv_cutProfile_eq_zero_of_gt h4, abs_zero]; exact le_max_right _ _
  have := hD s ⟨not_lt.1 h1, not_lt.1 h4⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-! ## Squared distance on the circle -/

/-- `‖e^{it} − p‖²` as an explicit real function of `t`. -/
def sqDist (p : ℂ) (t : ℝ) : ℝ := (Real.cos t - p.re) ^ 2 + (Real.sin t - p.im) ^ 2

/-- The derivative of `sqDist p`. -/
def sqDistDeriv (p : ℂ) (t : ℝ) : ℝ := 2 * (p.re * Real.sin t - p.im * Real.cos t)

theorem sqDist_eq (p : ℂ) (t : ℝ) : sqDist p t = ‖exp (t * I) - p‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sqDist]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  ring

theorem hasDerivAt_sqDist (p : ℂ) (t : ℝ) : HasDerivAt (sqDist p) (sqDistDeriv p t) t := by
  have h1 := ((Real.hasDerivAt_cos t).sub_const p.re).pow 2
  have h2 := ((Real.hasDerivAt_sin t).sub_const p.im).pow 2
  refine (h1.add h2).congr_deriv ?_
  simp only [sqDistDeriv, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

theorem continuous_sqDist (p : ℂ) : Continuous (sqDist p) := by unfold sqDist; fun_prop

theorem continuous_sqDistDeriv (p : ℂ) : Continuous (sqDistDeriv p) := by
  unfold sqDistDeriv; fun_prop

theorem abs_sqDistDeriv_le {p : ℂ} (hp : ‖p‖ = 1) (t : ℝ) :
    |sqDistDeriv p t| ≤ 2 * ‖exp (t * I) - p‖ := by
  have him : p.re * Real.sin t - p.im * Real.cos t = (conj p * (exp (t * I) - p)).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
      Complex.sub_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  rw [sqDistDeriv, abs_mul, abs_two, him]
  have := Complex.abs_im_le_norm (conj p * (exp (t * I) - p))
  rw [norm_mul, Complex.norm_conj, hp, one_mul] at this
  linarith

theorem sqDist_two_pi (p : ℂ) : sqDist p (2 * π) = sqDist p 0 := by
  simp [sqDist]

/-! ## The cutoff -/

/-- The cutoff `χ_δ(t) = ∏_{p ∈ E} η(‖e^{it} − p‖² / δ²)`. -/
def circCutoff (E : Finset ℂ) (δ : ℝ) (t : ℝ) : ℝ := ∏ p ∈ E, cutProfile (sqDist p t / δ ^ 2)

/-- The derivative of `circCutoff E δ`. -/
def circCutoffDeriv (E : Finset ℂ) (δ : ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ E, (∏ q ∈ E.erase p, cutProfile (sqDist q t / δ ^ 2)) *
    (deriv cutProfile (sqDist p t / δ ^ 2) * (sqDistDeriv p t / δ ^ 2))

theorem hasDerivAt_circCutoff (E : Finset ℂ) (δ t : ℝ) :
    HasDerivAt (circCutoff E δ) (circCutoffDeriv E δ t) t := by
  have h : ∀ p ∈ E, HasDerivAt (fun t => cutProfile (sqDist p t / δ ^ 2))
      (deriv cutProfile (sqDist p t / δ ^ 2) * (sqDistDeriv p t / δ ^ 2)) t := fun p _ =>
    (hasDerivAt_cutProfile _).comp t ((hasDerivAt_sqDist p t).div_const _)
  have := HasDerivAt.fun_finsetProd h
  simp only [smul_eq_mul] at this
  exact this

theorem continuous_circCutoff (E : Finset ℂ) (δ : ℝ) : Continuous (circCutoff E δ) := by
  unfold circCutoff
  exact continuous_finsetProd _ fun p _ =>
    (contDiff_cutProfile.continuous).comp ((continuous_sqDist p).div_const _)

theorem continuous_circCutoffDeriv (E : Finset ℂ) (δ : ℝ) : Continuous (circCutoffDeriv E δ) := by
  unfold circCutoffDeriv
  refine continuous_finsetSum _ fun p _ => ?_
  refine (continuous_finsetProd _ fun q _ =>
    (contDiff_cutProfile.continuous).comp ((continuous_sqDist q).div_const _)).mul ?_
  exact (continuous_deriv_cutProfile.comp ((continuous_sqDist p).div_const _)).mul
    ((continuous_sqDistDeriv p).div_const _)

theorem circCutoff_nonneg (E : Finset ℂ) (δ t : ℝ) : 0 ≤ circCutoff E δ t :=
  Finset.prod_nonneg fun _ _ => cutProfile_nonneg _

theorem circCutoff_le_one (E : Finset ℂ) (δ t : ℝ) : circCutoff E δ t ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => cutProfile_nonneg _) fun _ _ => cutProfile_le_one _

theorem circCutoff_two_pi (E : Finset ℂ) (δ : ℝ) : circCutoff E δ (2 * π) = circCutoff E δ 0 := by
  simp only [circCutoff, sqDist_two_pi]

/-- `χ_δ` vanishes within distance `δ` of `E`. -/
theorem circCutoff_eq_zero {E : Finset ℂ} {δ t : ℝ} (hδ : 0 < δ) {p : ℂ} (hp : p ∈ E)
    (ht : ‖exp (t * I) - p‖ < δ) : circCutoff E δ t = 0 := by
  refine Finset.prod_eq_zero hp (cutProfile_eq_zero ?_)
  rw [sqDist_eq, div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) ht.le 2

/-- `χ_δ = 1` at distance `> 2δ` from `E`, and its derivative vanishes there. -/
theorem circCutoff_eq_one {E : Finset ℂ} {δ t : ℝ} (hδ : 0 < δ)
    (ht : ∀ p ∈ E, 2 * δ < ‖exp (t * I) - p‖) :
    circCutoff E δ t = 1 ∧ circCutoffDeriv E δ t = 0 := by
  have hgt : ∀ p ∈ E, 4 < sqDist p t / δ ^ 2 := by
    intro p hp
    rw [sqDist_eq, lt_div_iff₀ (by positivity)]
    have := ht p hp
    nlinarith
  refine ⟨Finset.prod_eq_one fun p hp => cutProfile_eq_one (hgt p hp).le,
    Finset.sum_eq_zero fun p hp => ?_⟩
  rw [deriv_cutProfile_eq_zero_of_gt (hgt p hp)]
  ring

/-- **The derivative bound.** If `‖ψ(t)‖ ≤ L ‖e^{it} − p‖` for every `p ∈ E`, then
`‖ψ(t)‖ |χ_δ'(t)| ≤ 8 D L |E|`, where `D` bounds `η'`. -/
theorem mul_abs_circCutoffDeriv_le {E : Finset ℂ} (hE : ∀ p ∈ E, ‖p‖ = 1) {δ t : ℝ} (hδ : 0 < δ)
    {D L x : ℝ} (hD0 : 0 ≤ D) (hD : ∀ s, |deriv cutProfile s| ≤ D) (hL : 0 ≤ L) (hx0 : 0 ≤ x)
    (hx : ∀ p ∈ E, x ≤ L * ‖exp (t * I) - p‖) :
    x * |circCutoffDeriv E δ t| ≤ E.card * (8 * D * L) := by
  unfold circCutoffDeriv
  calc x * |∑ p ∈ E, (∏ q ∈ E.erase p, cutProfile (sqDist q t / δ ^ 2)) *
        (deriv cutProfile (sqDist p t / δ ^ 2) * (sqDistDeriv p t / δ ^ 2))|
      ≤ x * ∑ p ∈ E, |(∏ q ∈ E.erase p, cutProfile (sqDist q t / δ ^ 2)) *
        (deriv cutProfile (sqDist p t / δ ^ 2) * (sqDistDeriv p t / δ ^ 2))| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hx0
    _ = ∑ p ∈ E, x * |(∏ q ∈ E.erase p, cutProfile (sqDist q t / δ ^ 2)) *
        (deriv cutProfile (sqDist p t / δ ^ 2) * (sqDistDeriv p t / δ ^ 2))| := Finset.mul_sum _ _ _
    _ ≤ ∑ _p ∈ E, 8 * D * L := Finset.sum_le_sum fun p hp => ?_
    _ = E.card * (8 * D * L) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hprod0 : 0 ≤ ∏ q ∈ E.erase p, cutProfile (sqDist q t / δ ^ 2) :=
    Finset.prod_nonneg fun _ _ => cutProfile_nonneg _
  have hprod1 : ∏ q ∈ E.erase p, cutProfile (sqDist q t / δ ^ 2) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => cutProfile_nonneg _) fun _ _ => cutProfile_le_one _
  by_cases h4 : 4 < sqDist p t / δ ^ 2
  · rw [deriv_cutProfile_eq_zero_of_gt h4]; simp only [zero_mul, mul_zero, abs_zero]; positivity
  simp only [not_lt] at h4
  set d := ‖exp (t * I) - p‖ with hd
  have hd2 : d ^ 2 ≤ 4 * δ ^ 2 := by
    rw [sqDist_eq, div_le_iff₀ (by positivity)] at h4; linarith
  have hdd := abs_sqDistDeriv_le (hE p hp) t
  rw [← hd] at hdd
  have hxp := hx p hp
  rw [← hd] at hxp
  have hd0 : 0 ≤ d := norm_nonneg _
  rw [abs_mul, abs_mul, abs_div, abs_of_nonneg hprod0, abs_of_pos (by positivity : 0 < δ ^ 2)]
  have hδ2 : 0 < δ ^ 2 := by positivity
  calc x * ((∏ q ∈ E.erase p, cutProfile (sqDist q t / δ ^ 2)) *
        (|deriv cutProfile (sqDist p t / δ ^ 2)| * (|sqDistDeriv p t| / δ ^ 2)))
      ≤ (L * d) * (1 * (D * (2 * d / δ ^ 2))) := by
        gcongr
        · exact hD _
    _ = 2 * D * L * (d ^ 2 / δ ^ 2) := by ring
    _ ≤ 2 * D * L * 4 := by
        gcongr
        rw [div_le_iff₀ hδ2]; linarith
    _ = 8 * D * L := by ring

end InteractingSLE.Sec6
