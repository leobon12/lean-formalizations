/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiExistsRiesz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The fourth-moment bound `E (U_t - U_s)^4 ≤ M (t - s)^2`

Packet PROVE-YW-JACOBI. With `q_z = (X - z)^4` (`quartic z`), the two-time formula gives
`E (U_t - U_s)^4 = ∫ (semi (t - s) q_z)(z) dπ(z)`. The function `φ(r) = (semi r q_z)(z)` satisfies
`φ(0) = q_z(z) = 0`, `φ'(0) = (L q_z)(z) = 0` (`q_z` vanishes to fourth order at `z`) and
`|φ''(r)| = |(semi r (L² q_z))(z)| ≤ M` (contraction, `abs_semi_eval_le`), so `|φ(h)| ≤ M h²`
(`abs_semi_quartic_le`, two mean-value estimates). Hence `integral_quartic_le`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Polynomial

namespace InteractingSLE

namespace Sec2

namespace JacobiExists

theorem exists_bound_on_Icc (p : ℝ[X]) : ∃ B, ∀ y ∈ Icc (0 : ℝ) 1, |p.eval y| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  exact ⟨B, fun y hy => by simpa [Real.norm_eq_abs] using hB y hy⟩

/-- The quartic `(X - z)^4`. -/
def quartic (z : ℝ) : ℝ[X] := (X - C z) ^ 4

theorem quartic_expand (z : ℝ) :
    quartic z = X ^ 4 - C (4 * z) * X ^ 3 + C (6 * z ^ 2) * X ^ 2 - C (4 * z ^ 3) * X +
      C (z ^ 4) := by
  refine Polynomial.funext fun y => ?_
  simp only [quartic, eval_pow, eval_sub, eval_X, eval_C, eval_add, eval_mul]
  ring

variable {κ a b : ℝ}

theorem genL_C_mul' (c : ℝ) (p : ℝ[X]) : genL κ a b (C c * p) = C c * genL κ a b p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]

theorem genL_quartic_eval_self (z : ℝ) : (genL κ a b (quartic z)).eval z = 0 := by
  rw [eval_genL, quartic, derivative_X_sub_C_pow, derivative_C_mul, derivative_X_sub_C_pow]
  simp

theorem exists_bound_genL_genL_quartic :
    ∃ M, 0 ≤ M ∧ ∀ z ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |(genL κ a b (genL κ a b (quartic z))).eval y| ≤ M := by
  obtain ⟨B4, h4⟩ := exists_bound_on_Icc (genL κ a b (genL κ a b (X ^ 4)))
  obtain ⟨B3, h3⟩ := exists_bound_on_Icc (genL κ a b (genL κ a b (X ^ 3)))
  obtain ⟨B2, h2⟩ := exists_bound_on_Icc (genL κ a b (genL κ a b (X ^ 2)))
  obtain ⟨B1, h1⟩ := exists_bound_on_Icc (genL κ a b (genL κ a b X))
  refine ⟨|B4| + 4 * |B3| + 6 * |B2| + 4 * |B1|, by positivity, fun z hz y hy => ?_⟩
  have e : genL κ a b (genL κ a b (quartic z)) = genL κ a b (genL κ a b (X ^ 4)) -
      C (4 * z) * genL κ a b (genL κ a b (X ^ 3)) + C (6 * z ^ 2) * genL κ a b (genL κ a b (X ^ 2)) -
      C (4 * z ^ 3) * genL κ a b (genL κ a b X) := by
    rw [quartic_expand]
    simp only [map_add, map_sub, genL_C_mul', genL_C, add_zero]
  rw [e]
  simp only [eval_add, eval_sub, eval_mul, eval_C]
  have hz0 := hz.1
  have hz1 := hz.2
  have a1 : |4 * z * (genL κ a b (genL κ a b (X ^ 3))).eval y| ≤ 4 * |B3| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 4 * z)]
    have := (h3 y hy).trans (le_abs_self B3)
    nlinarith [abs_nonneg ((genL κ a b (genL κ a b (X ^ 3))).eval y)]
  have a2 : |6 * z ^ 2 * (genL κ a b (genL κ a b (X ^ 2))).eval y| ≤ 6 * |B2| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 6 * z ^ 2)]
    have := (h2 y hy).trans (le_abs_self B2)
    have hz2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
    nlinarith [abs_nonneg ((genL κ a b (genL κ a b (X ^ 2))).eval y)]
  have a3 : |4 * z ^ 3 * (genL κ a b (genL κ a b X)).eval y| ≤ 4 * |B1| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * z ^ 3)]
    have := (h1 y hy).trans (le_abs_self B1)
    have hz3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
    nlinarith [abs_nonneg ((genL κ a b (genL κ a b X)).eval y)]
  have a0 := (h4 y hy).trans (le_abs_self B4)
  calc _ ≤ |(genL κ a b (genL κ a b (X ^ 4))).eval y| +
        |4 * z * (genL κ a b (genL κ a b (X ^ 3))).eval y| +
        |6 * z ^ 2 * (genL κ a b (genL κ a b (X ^ 2))).eval y| +
        |4 * z ^ 3 * (genL κ a b (genL κ a b X)).eval y| := by
        refine (abs_sub _ _).trans ?_
        refine add_le_add ((abs_add_le _ _).trans ?_) le_rfl
        exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ _ := by linarith

/-- **The semigroup on the quartic.** `|(semi h q_z)(z)| ≤ M h²` for `h ≥ 0`, `z ∈ [0, 1]`. -/
theorem abs_semi_quartic_le (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    ∃ M, 0 ≤ M ∧ ∀ h, 0 ≤ h → ∀ z ∈ Icc (0 : ℝ) 1,
      |(semi κ a b h (quartic z)).eval z| ≤ M * h ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_genL_genL_quartic (κ := κ) (a := a) (b := b)
  refine ⟨M, hM0, fun h hh z hz => ?_⟩
  set q := quartic z
  -- `ψ r = (semi r (L q))(z)`, `ψ' r = (semi r (L² q))(z)`
  have hψ : ∀ r, HasDerivAt (fun r => (semi κ a b r (genL κ a b q)).eval z)
      ((semi κ a b r (genL κ a b (genL κ a b q))).eval z) r := fun r => by
    have := hasDerivAt_eval_semi κ a b (genL κ a b q) z r
    rwa [← semi_genL] at this
  have hφ : ∀ r, HasDerivAt (fun r => (semi κ a b r q).eval z)
      ((semi κ a b r (genL κ a b q)).eval z) r := fun r => by
    have := hasDerivAt_eval_semi κ a b q z r
    rwa [← semi_genL] at this
  have hψbound : ∀ r ∈ Icc (0 : ℝ) h, |(semi κ a b r (genL κ a b q)).eval z| ≤ M * r := by
    intro r hr
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r =>
      (semi κ a b r (genL κ a b q)).eval z) (a := 0) (b := r) (C := M)
      (fun x _ => (hψ x).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs]
        exact abs_semi_eval_le hκ.le ha.le hb.le (fun y hy => hM z hz y hy) hx.1 hz)
      r ⟨hr.1, le_rfl⟩
    simp only [semi_zero_time, genL_quartic_eval_self, sub_zero, Real.norm_eq_abs, q] at this
    simpa [q] using this
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r => (semi κ a b r q).eval z)
    (a := 0) (b := h) (C := M * h) (fun x _ => (hφ x).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      refine (hψbound x ⟨hx.1, hx.2.le⟩).trans ?_
      exact mul_le_mul_of_nonneg_left hx.2.le hM0)
    h ⟨hh, le_rfl⟩
  simp only [semi_zero_time, Real.norm_eq_abs, sub_zero, q, quartic, eval_pow, eval_sub, eval_X,
    eval_C, sub_self] at this
  rw [show M * h ^ 2 = M * h * h by ring]
  simpa [q, quartic] using this

theorem slice_quartic (s t : ℝ) (hst : s ≠ t) (z : ℝ) :
    slice t (Function.update 0 s z)
      ((MvPolynomial.X t - MvPolynomial.X s : MvPolynomial ℝ ℝ) ^ 4) = quartic z := by
  simp only [map_pow, map_sub, slice_X, Function.update_self, Function.update_of_ne hst, quartic]

theorem vars_quartic_subset (s t : ℝ) :
    ((MvPolynomial.X t - MvPolynomial.X s : MvPolynomial ℝ ℝ) ^ 4).vars ⊆ {s, t} := by
  classical
  refine (MvPolynomial.vars_pow _ 4).trans ?_
  refine (MvPolynomial.vars_sub_subset (p := MvPolynomial.X t) (q := MvPolynomial.X s)).trans ?_
  rw [MvPolynomial.vars_X, MvPolynomial.vars_X]
  intro d hd
  simp only [Finset.mem_union, Finset.mem_singleton] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **The fourth-moment bound.** -/
theorem integral_quartic_le (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    ∃ M, 0 ≤ M ∧ ∀ s t : ℝ, ∫ ω, (toConfig ω t - toConfig ω s) ^ 4 ∂(pathMeasure κ a b hκ ha hb) ≤
      M * (t - s) ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := abs_semi_quartic_le hκ ha hb
  have := isProbabilityMeasure_invLaw hκ ha hb
  have key : ∀ s t : ℝ, s < t →
      ∫ ω, (toConfig ω t - toConfig ω s) ^ 4 ∂(pathMeasure κ a b hκ ha hb) ≤ M * (t - s) ^ 2 := by
    intro s t hst
    have h1 := integral_eval_pathMeasure hκ ha hb
      ((MvPolynomial.X t - MvPolynomial.X s : MvPolynomial ℝ ℝ) ^ 4)
    simp only [map_pow, map_sub, MvPolynomial.eval_X] at h1
    rw [h1, lam_two hκ ha hb hst (fun d hd => by
      have := vars_quartic_subset s t hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      exact this)]
    simp only [slice_quartic s t hst.ne]
    have h2 : ∀ᵐ z ∂(invLaw κ a b), (semi κ a b (t - s) (quartic z)).eval z ≤ M * (t - s) ^ 2 :=
      (ae_mem_Icc_invLaw κ a b).mono fun z hz =>
        (le_abs_self _).trans (hM (t - s) (by linarith) z hz)
    have h0 : 0 ≤ᵐ[invLaw κ a b] fun z => (semi κ a b (t - s) (quartic z)).eval z :=
      (ae_mem_Icc_invLaw κ a b).mono fun z hz => semi_eval_nonneg hκ.le ha.le hb.le
        (fun y _ => by simp only [quartic, eval_pow, eval_sub, eval_X, eval_C]; positivity)
        (by linarith) hz
    calc _ ≤ ∫ _z, M * (t - s) ^ 2 ∂(invLaw κ a b) :=
          integral_mono_of_nonneg h0 (integrable_const _) h2
      _ = M * (t - s) ^ 2 := by simp
  refine ⟨M, hM0, fun s t => ?_⟩
  rcases lt_trichotomy s t with h | rfl | h
  · exact key s t h
  · simp
  · have := key t s h
    calc _ = ∫ ω, (toConfig ω s - toConfig ω t) ^ 4 ∂(pathMeasure κ a b hκ ha hb) := by
          congr 1; funext ω; ring
      _ ≤ M * (s - t) ^ 2 := this
      _ = M * (t - s) ^ 2 := by ring

end JacobiExists

end Sec2

end InteractingSLE
