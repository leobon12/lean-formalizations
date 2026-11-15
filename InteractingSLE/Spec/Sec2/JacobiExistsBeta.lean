/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiExistsPositive
import InteractingSLE.Spec.Sec2.JacobiMoments
import Mathlib.Probability.Distributions.Beta

/-!
# The beta law is invariant for the Jacobi semigroup

Packet PROVE-YW-JACOBI. Specification p. 22, L504–L506: the invariant law of the Jacobi diffusion is
`π(du) = u^{2a/κ - 1} (1 - u)^{2b/κ - 1} / B(2a/κ, 2b/κ) du`. Here `π = betaMeasure (2a/κ) (2b/κ)`
(`invLaw`). Its moments are the landed `jacobiMoment κ a b n` (`integral_pow_invLaw`: the ratio of
consecutive beta moments `(α + n)/(α + β + n)` is the ratio `d_{n+1}/(-c_{n+1})` of the moment
recursion), so `∫ L p dπ = 0` for every polynomial (`integral_genL_invLaw`, from
`ccoef_mul_jacobiMoment_add`), and `π` is invariant: `∫ semi t p dπ = ∫ p dπ`
(`integral_semi_invLaw`). Being a probability measure carried by `[0, 1]`, `π` is a positive
normalized functional on polynomials (`integral_eval_invLaw_nonneg`).

The beta-moment computation follows the one of `WangWu/SeedJacobi.lean` (packet PROVE-WW-C, written for
`κ = 2`), restated here for every `κ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Polynomial Set Filter Topology

namespace InteractingSLE

namespace Sec2

namespace JacobiExists

/-! ### Beta densities -/

theorem betaPDFReal_nonneg' {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (x : ℝ) : 0 ≤ betaPDFReal A B x := by
  unfold betaPDFReal
  split_ifs with h
  · have := beta_pos hA hB
    have h1 : 0 ≤ x ^ (A - 1) := Real.rpow_nonneg h.1.le _
    have h2 : 0 ≤ (1 - x) ^ (B - 1) := Real.rpow_nonneg (by linarith [h.2]) _
    positivity
  · exact le_rfl

theorem integral_betaPDFReal_eq_one' {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫ x, betaPDFReal A B x = 1 := by
  have h := lintegral_betaPDF_eq_one hA hB
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => betaPDFReal_nonneg' hA hB x)
    (measurable_betaPDFReal A B).aestronglyMeasurable]
  simp only [betaPDF] at h
  rw [h, ENNReal.toReal_one]

theorem betaPDFReal_mul_pow' {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) (x : ℝ) :
    betaPDFReal A B x * x ^ n = beta (A + n) B / beta A B * betaPDFReal (A + n) B x := by
  unfold betaPDFReal
  split_ifs with h
  · have hx : x ≠ 0 := h.1.ne'
    have hb := beta_pos hA hB
    have hb' := beta_pos (by positivity : 0 < A + n) hB
    have e : x ^ (A + n - 1) = x ^ (A - 1) * x ^ n := by
      rw [show A + n - 1 = (A - 1) + (n : ℝ) by ring, Real.rpow_add_natCast hx]
    rw [e]
    field_simp
  · simp

theorem beta_succ_div' {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    beta (A + (n + 1 : ℕ)) B = beta (A + n) B * ((A + n) / (A + n + B)) := by
  have h1 : 0 < A + n := by positivity
  have h2 : 0 < A + n + B := by positivity
  unfold beta
  have e1 : A + ((n + 1 : ℕ) : ℝ) = (A + n) + 1 := by push_cast; ring
  rw [e1, show A + n + 1 + B = (A + n + B) + 1 by ring, Real.Gamma_add_one h1.ne',
    Real.Gamma_add_one h2.ne']
  have g1 := Real.Gamma_pos_of_pos h1
  have g2 := Real.Gamma_pos_of_pos h2
  have g3 := Real.Gamma_pos_of_pos hB
  field_simp

theorem integral_pow_betaMeasure' {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    ∫ x, x ^ n ∂(betaMeasure A B) = beta (A + n) B / beta A B := by
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (betaPDF A B) from (measurable_betaPDFReal A B).ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [betaPDF, ENNReal.toReal_ofReal (betaPDFReal_nonneg' hA hB _), smul_eq_mul,
    betaPDFReal_mul_pow' hA hB n, integral_const_mul,
    integral_betaPDFReal_eq_one' (by positivity : 0 < A + n) hB, mul_one]

/-! ### The invariant law -/

/-- The invariant law `π = Beta(2a/κ, 2b/κ)`. -/
def invLaw (κ a b : ℝ) : Measure ℝ := betaMeasure (2 * a / κ) (2 * b / κ)

variable {κ a b : ℝ}

theorem isProbabilityMeasure_invLaw (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (invLaw κ a b) :=
  isProbabilityMeasureBeta (by positivity) (by positivity)

theorem measurable_betaPDF' (A B : ℝ) : Measurable (betaPDF A B) :=
  (measurable_betaPDFReal A B).ennreal_ofReal

theorem ae_mem_Icc_invLaw (κ a b : ℝ) : ∀ᵐ x ∂(invLaw κ a b), x ∈ Icc (0 : ℝ) 1 := by
  rw [invLaw, betaMeasure, ae_withDensity_iff (measurable_betaPDF' _ _)]
  refine ae_of_all _ fun x hx => ?_
  by_contra hxI
  apply hx
  simp only [betaPDF, ENNReal.ofReal_eq_zero, betaPDFReal]
  rw [ite_eq_right_iff.mpr (fun h => absurd h ?_)]
  rintro ⟨h0, h1⟩
  exact hxI ⟨h0.le, h1.le⟩

theorem integrable_eval_invLaw (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (p : ℝ[X]) :
    Integrable (fun x => p.eval x) (invLaw κ a b) := by
  have := isProbabilityMeasure_invLaw hκ ha hb
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  refine Integrable.of_bound (C := M) p.continuous.aestronglyMeasurable ?_
  filter_upwards [ae_mem_Icc_invLaw κ a b] with x hx
  exact hM x hx

/-- **The moments of `π`** are the landed `jacobiMoment κ a b n`. -/
theorem integral_pow_invLaw (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∫ x, x ^ n ∂(invLaw κ a b) = Jacobi.jacobiMoment κ a b n := by
  set A := 2 * a / κ
  set B := 2 * b / κ
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hmom : ∀ n : ℕ, ∫ x, x ^ n ∂(invLaw κ a b) = beta (A + n) B / beta A B :=
    fun n => integral_pow_betaMeasure' hA hB n
  rw [hmom]
  have hbeta := beta_pos hA hB
  induction n with
  | zero => simp [Jacobi.jacobiMoment, hbeta.ne']
  | succ n ih =>
    rw [Jacobi.jacobiMoment, ← ih, beta_succ_div' hA hB n, Jacobi.dcoef, Jacobi.ccoef]
    have h2 : 0 < A + n + B := by positivity
    have hr : (κ / 4 * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1)) + ((n + 1 : ℕ) : ℝ) * a / 2) /
        -(-(κ / 4 * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1)) +
          ((n + 1 : ℕ) : ℝ) * (a + b) / 2)) = (A + n) / (A + n + B) := by
      have hn : (0 : ℝ) < n + 1 := by positivity
      push_cast
      have hd : 0 < κ / 4 * (((n : ℝ) + 1) * ((n : ℝ) + 1 - 1)) + ((n : ℝ) + 1) * (a + b) / 2 := by
        rw [add_sub_cancel_right]; positivity
      rw [div_eq_div_iff (by rw [neg_neg]; exact hd.ne') h2.ne']
      simp only [A, B]
      field_simp
      ring
    rw [hr]
    field_simp

/-- `∫ p dπ = ∑ₖ pₖ mₖ` for a polynomial of degree `< N`. -/
theorem integral_eval_invLaw_eq_sum (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {N : ℕ} {p : ℝ[X]}
    (hp : p ∈ degreeLT ℝ N) :
    ∫ x, p.eval x ∂(invLaw κ a b) = ∑ k ∈ Finset.range N, p.coeff k * Jacobi.jacobiMoment κ a b k := by
  have e : ∀ x, p.eval x = ∑ k ∈ Finset.range N, p.coeff k * x ^ k := fun x =>
    eval_eq_sum_of_mem hp x
  simp only [e]
  rw [integral_finsetSum _ (fun k _ => ((integrable_eval_invLaw hκ ha hb (X ^ k)).congr
    (ae_of_all _ fun x => by simp)).const_mul _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_pow_invLaw hκ ha hb]

/-- **`∫ L p dπ = 0`.** -/
theorem integral_genL_invLaw (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (p : ℝ[X]) :
    ∫ x, (genL κ a b p).eval x ∂(invLaw κ a b) = 0 := by
  set N := p.natDegree + 1
  have hp := mem_degreeLT_natDegree_succ p
  have e : genL κ a b p = ∑ k ∈ Finset.range N, C (p.coeff k) * genL κ a b (X ^ k) := by
    conv_lhs => rw [eq_sum_of_mem_degreeLT hp]
    simp only [map_sum, ← smul_eq_C_mul, map_smul]
    rfl
  have hint : ∀ q : ℝ[X], Integrable (fun x => q.eval x) (invLaw κ a b) :=
    integrable_eval_invLaw hκ ha hb
  rw [e]
  simp only [eval_finsetSum, eval_mul, eval_C]
  rw [integral_finsetSum _ (fun k _ => (hint _).const_mul _)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul]
  rcases k with _ | n
  · have : genL κ a b 1 = 0 := by simpa using genL_C κ a b 1
    simp [this]
  · rw [genL_X_pow, integral_eval_invLaw_eq_sum hκ ha hb (N := n + 2)]
    · have hc := Jacobi.ccoef_mul_jacobiMoment_add hκ.le (by linarith) (κ := κ) (a := a) (b := b) n
      simp only [Jacobi.ccoef, Jacobi.dcoef] at hc
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero]
      · simp only [coeff_add, coeff_C_mul, coeff_X_pow, Nat.add_sub_cancel]
        simp only [show n + 1 ≠ n by omega, ite_false, ite_true, mul_zero, zero_add, add_zero,
          mul_one, show n ≠ n + 1 by omega]
        push_cast at hc ⊢
        rw [mul_eq_zero]
        right
        linarith
      · intro k hk
        simp only [Finset.mem_range] at hk
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, show k ≠ n + 1 - 1 by omega,
          show k ≠ n + 1 by omega, ite_false, mul_zero, add_zero, zero_mul]
    · refine Submodule.add_mem _ ?_ ?_ <;> rw [← smul_eq_C_mul] <;>
        refine Submodule.smul_mem _ _ (mem_degreeLT.2 ?_) <;>
        simp only [degree_X_pow] <;> exact_mod_cast (by omega)

/-- **Invariance of `π`**: `∫ semi t p dπ = ∫ p dπ`. -/
theorem integral_semi_invLaw (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) (p : ℝ[X]) :
    ∫ x, (semi κ a b t p).eval x ∂(invLaw κ a b) = ∫ x, p.eval x ∂(invLaw κ a b) := by
  set N := p.natDegree + 1
  have hmem : ∀ s, semi κ a b s p ∈ degreeLT ℝ N := fun s => semi_mem_degreeLT_succ κ a b s p
  have e : ∀ s, ∫ x, (semi κ a b s p).eval x ∂(invLaw κ a b) =
      ∑ k ∈ Finset.range N, (semi κ a b s p).coeff k * Jacobi.jacobiMoment κ a b k :=
    fun s => integral_eval_invLaw_eq_sum hκ ha hb (hmem s)
  have hder : ∀ s, HasDerivAt (fun s => ∫ x, (semi κ a b s p).eval x ∂(invLaw κ a b)) 0 s := by
    intro s
    simp only [e]
    have h0 : (0 : ℝ) = ∑ k ∈ Finset.range N,
        (genL κ a b (semi κ a b s p)).coeff k * Jacobi.jacobiMoment κ a b k := by
      rw [← integral_eval_invLaw_eq_sum hκ ha hb (genL_mem_degreeLT κ a b (hmem s)),
        integral_genL_invLaw hκ ha hb]
    rw [h0]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_coeff_semi κ a b p s k).mul_const _
  have := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simpa using this

/-- Positivity of `π` on polynomials. -/
theorem integral_eval_invLaw_nonneg {p : ℝ[X]} (hp : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ p.eval x) :
    0 ≤ ∫ x, p.eval x ∂(invLaw κ a b) :=
  integral_nonneg_of_ae ((ae_mem_Icc_invLaw κ a b).mono fun x hx => hp x hx)

theorem abs_integral_eval_invLaw_le (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {p : ℝ[X]} {M : ℝ}
    (hp : ∀ x ∈ Icc (0 : ℝ) 1, |p.eval x| ≤ M) : |∫ x, p.eval x ∂(invLaw κ a b)| ≤ M := by
  have := isProbabilityMeasure_invLaw hκ ha hb
  have h := norm_integral_le_of_norm_le_const (μ := invLaw κ a b) (C := M)
    (f := fun x => p.eval x) ((ae_mem_Icc_invLaw κ a b).mono fun x hx => hp x hx)
  simpa [probReal_univ] using h

end JacobiExists

end Sec2

end InteractingSLE
