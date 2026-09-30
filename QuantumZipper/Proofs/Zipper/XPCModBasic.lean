import QuantumZipper.Proofs.Zipper.XAreaPCModI

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc, R1 for the pushed circles (1/2): the divided difference of a univalent map

Let `ψ` be holomorphic and injective on an open `U`, with `ψ' ≠ 0` there, and let `K ⊆ U` be
convex and compact. The divided difference

  `ddq ψ x y = ∫₀¹ ψ'(y + τ (x − y)) dτ`,   `ddq ψ x y · (x − y) = ψ x − ψ y` (`ddq_mul`),

is Lipschitz on `K × K` (`ddq_lip`, from a bound on `ψ''`), never vanishes there (`ψ'` on the
diagonal, injectivity off it) and hence is bounded below by some `m > 0`
(`exists_ddq_lower`). Consequently the correction kernel

  `qt ψ x y = −log‖ddq ψ x y‖ − log‖ψ x − conj (ψ y)‖ + log‖x − conj y‖`

satisfies `neumannH (ψ x) (ψ y) = neumannH x y + qt ψ x y` for `x ≠ y` in `K` (`neumannH_eq_add_qt`),
and is bounded and Lipschitz in its second variable on `K` (`exists_qt_bounds`), provided
`K ⊆ ℍ` and `ψ(K) ⊆ ℍ`.

This is the elementary two-variable form of the classical fact that
`log((f(z) − f(ζ))/(z − ζ))` is holomorphic in both variables for univalent `f` (Pommerenke,
*Univalent Functions*, §1.3 / Grunsky coefficients); the version used here (divided difference by
the fundamental theorem of calculus, compactness for the lower bound) is an own elementary
argument (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ComplexConjugate

namespace QuantumZipper.E6
namespace XAreaPC

theorem xpm_abs_log_sub_le {m a b : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have key : ∀ a b : ℝ, m ≤ a → m ≤ b → Real.log a - Real.log b ≤ |a - b| / m := by
    intro a b ha hb
    have ha0 : 0 < a := hm.trans_le ha
    have hb0 : 0 < b := hm.trans_le hb
    rw [← Real.log_div ha0.ne' hb0.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    have h2 : a / b - 1 = (a - b) / b := by field_simp
    have h3 : (a - b) / b ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
    have h4 : |a - b| / b ≤ |a - b| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hb
    linarith
  rw [abs_le]
  refine ⟨?_, key a b ha hb⟩
  have := key b a hb ha
  rw [abs_sub_comm] at this
  linarith

theorem xpm_im_add_le_norm_sub_conj (a b : ℂ) : a.im + b.im ≤ ‖a - conj b‖ := by
  have := RCLike.abs_im_le_norm (a - conj b)
  simp only [RCLike.im_to_complex, Complex.sub_im, Complex.conj_im, sub_neg_eq_add] at this
  linarith [le_abs_self (a.im + b.im)]

theorem xpm_seg_mem {K : Set ℂ} (hK : Convex ℝ K) {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : y + (τ : ℂ) * (x - y) ∈ K := by
  have := hK.add_smul_sub_mem hy hx hτ
  rwa [Complex.real_smul] at this

/-- The divided difference `∫₀¹ ψ'(y + τ (x − y)) dτ`. -/
def ddq (ψ : ℂ → ℂ) (x y : ℂ) : ℂ := ∫ τ in (0 : ℝ)..1, deriv ψ (y + (τ : ℂ) * (x - y))

theorem ddq_self (ψ : ℂ → ℂ) (x : ℂ) : ddq ψ x x = deriv ψ x := by
  simp [ddq]

section DD

variable {ψ : ℂ → ℂ} {U K : Set ℂ}

theorem ddq_intervalIntegrable (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) (hK : Convex ℝ K)
    (hKU : K ⊆ U) {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) :
    IntervalIntegrable (fun τ : ℝ => deriv ψ (y + (τ : ℂ) * (x - y))) volume 0 1 := by
  have hd : ContinuousOn (deriv ψ) U := (hψ.analyticOnNhd hU).deriv.continuousOn
  have hp : Continuous fun τ : ℝ => y + (τ : ℂ) * (x - y) := by fun_prop
  refine ContinuousOn.intervalIntegrable ?_
  refine (hd.mono hKU).comp hp.continuousOn fun τ hτ => ?_
  exact xpm_seg_mem hK hx hy (by rwa [uIcc_of_le zero_le_one] at hτ)

theorem ddq_mul (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) (hK : Convex ℝ K) (hKU : K ⊆ U)
    {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) : ddq ψ x y * (x - y) = ψ x - ψ y := by
  have hmem : ∀ τ ∈ uIcc (0 : ℝ) 1, y + (τ : ℂ) * (x - y) ∈ K := fun τ hτ =>
    xpm_seg_mem hK hx hy (by rwa [uIcc_of_le zero_le_one] at hτ)
  have hderiv : ∀ τ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun τ : ℝ => ψ (y + (τ : ℂ) * (x - y)))
      (deriv ψ (y + (τ : ℂ) * (x - y)) * (x - y)) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun τ : ℝ => y + (τ : ℂ) * (x - y)) (x - y) τ := by
      have := (((hasDerivAt_id τ).ofReal_comp).mul_const (x - y)).const_add y
      simpa using this
    have h2 : HasDerivAt ψ (deriv ψ (y + (τ : ℂ) * (x - y))) (y + (τ : ℂ) * (x - y)) :=
      (hψ.differentiableAt (hU.mem_nhds (hKU (hmem τ hτ)))).hasDerivAt
    exact h2.comp τ h1
  have hint := (ddq_intervalIntegrable hU hψ hK hKU hx hy).mul_const (x - y)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [ddq, ← intervalIntegral.integral_mul_const, this]
  simp

theorem ddq_lip (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) (hK : Convex ℝ K) (hKU : K ⊆ U)
    {M₂ : ℝ} (hM₂0 : 0 ≤ M₂) (hM₂ : ∀ u ∈ K, ‖deriv (deriv ψ) u‖ ≤ M₂)
    {x y x' y' : ℂ} (hx : x ∈ K) (hy : y ∈ K) (hx' : x' ∈ K) (hy' : y' ∈ K) :
    ‖ddq ψ x y - ddq ψ x' y'‖ ≤ M₂ * (‖x - x'‖ + ‖y - y'‖) := by
  have hA : AnalyticOnNhd ℂ ψ U := hψ.analyticOnNhd hU
  have hL : ∀ a ∈ K, ∀ b ∈ K, ‖deriv ψ a - deriv ψ b‖ ≤ M₂ * ‖a - b‖ := fun a ha b hb =>
    hK.norm_image_sub_le_of_norm_deriv_le (f := deriv ψ) (C := M₂)
      (fun u hu => (hA.deriv u (hKU hu)).differentiableAt) hM₂ hb ha
  rw [ddq, ddq, ← intervalIntegral.integral_sub (ddq_intervalIntegrable hU hψ hK hKU hx hy)
    (ddq_intervalIntegrable hU hψ hK hKU hx' hy')]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := M₂ * (‖x - x'‖ + ‖y - y'‖))
    (f := fun τ : ℝ => deriv ψ (y + (τ : ℂ) * (x - y)) - deriv ψ (y' + (τ : ℂ) * (x' - y')))
    (fun τ hτ => by
      rw [uIoc_of_le zero_le_one] at hτ
      have hτ' : τ ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hτ
      refine (hL _ (xpm_seg_mem hK hx hy hτ') _ (xpm_seg_mem hK hx' hy' hτ')).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hM₂0
      have e : y + (τ : ℂ) * (x - y) - (y' + (τ : ℂ) * (x' - y')) =
          ((1 - τ : ℝ) : ℂ) * (y - y') + (τ : ℂ) * (x - x') := by push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.2 hτ'.2), Real.norm_of_nonneg hτ'.1]
      nlinarith [norm_nonneg (x - x'), norm_nonneg (y - y'), hτ'.1, hτ'.2])
  simpa using this

end DD

/-- The correction kernel: `neumannH (ψ x) (ψ y) − neumannH x y` off the diagonal. -/
def qt (ψ : ℂ → ℂ) (x y : ℂ) : ℝ :=
  -Real.log ‖ddq ψ x y‖ - Real.log ‖ψ x - conj (ψ y)‖ + Real.log ‖x - conj y‖

end XAreaPC
end QuantumZipper.E6
