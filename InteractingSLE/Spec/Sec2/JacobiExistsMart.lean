/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiExistsPath
import InteractingSLE.Spec.Sec2.TwoSeedExistsPath

/-!
# The constructed process solves the Jacobi martingale problem

Packet PROVE-YW-JACOBI. Under `pathMeasure κ a b`, the continuous process `U = jacU κ a b` solves the
landed polynomial martingale problem `Jacobi.IsJacobiMP κ a b` (`isJacobiMP_jacU`):

* mixed moments `E[∏ U_{s_i}^{k_i} f(U_x)] = lam (∏ X_{s_i}^{k_i} · f(X_x))` (`integral_prod_mul_eval`):
  `U` is a modification of the coordinate process;
* for `s_i ≤ w ≤ v`: `lam(G f(X_v)) - lam(G f(X_w)) = ∫_w^v lam(G (L f)(X_x)) dx`
  (`lam_mul_aeval_sub`): the Markov property turns `x ↦ lam(G f(X_x))` into
  `x ↦ lam(G (semi (x - w) f)(X_w))`, whose derivative is `lam(G (L semi (x - w) f)(X_w))
  = lam(G (L f)(X_x))`;
* Fubini for the time integral (`integral_mul_intervalIntegral`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace InteractingSLE

namespace Sec2

namespace JacobiExists

variable {κ a b : ℝ}

/-- The polynomial `∏ X_{s_i}^{k_i}`. -/
def prodX {m : ℕ} (s : Fin m → ℝ) (k : Fin m → ℕ) : MvPolynomial ℝ ℝ :=
  ∏ i, (MvPolynomial.X (s i) : MvPolynomial ℝ ℝ) ^ k i

theorem eval_prodX {m : ℕ} (s : Fin m → ℝ) (k : Fin m → ℕ) (y : ℝ → ℝ) :
    MvPolynomial.eval y (prodX s k) = ∏ i, y (s i) ^ k i := by
  simp [prodX, map_prod]

theorem vars_prodX {m : ℕ} (s : Fin m → ℝ) (k : Fin m → ℕ) :
    ∀ d ∈ (prodX s k).vars, ∃ i, d = s i := by
  classical
  intro d hd
  have h := MvPolynomial.vars_prod (s := Finset.univ)
    (f := fun i => (MvPolynomial.X (s i) : MvPolynomial ℝ ℝ) ^ k i) hd
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h
  obtain ⟨i, hi⟩ := h
  have := MvPolynomial.vars_pow _ _ hi
  rw [MvPolynomial.vars_X, Finset.mem_singleton] at this
  exact ⟨i, this⟩

/-- **The moment identity in time.** -/
theorem lam_mul_aeval_sub (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {G : MvPolynomial ℝ ℝ}
    {w v : ℝ} (hwv : w ≤ v) (hG : ∀ d ∈ G.vars, d ≤ w) (f : Polynomial ℝ) :
    lam κ a b (G * Polynomial.aeval (MvPolynomial.X v : MvPolynomial ℝ ℝ) f) -
        lam κ a b (G * Polynomial.aeval (MvPolynomial.X w : MvPolynomial ℝ ℝ) f) =
      ∫ x in w..v, lam κ a b (G * Polynomial.aeval (MvPolynomial.X x : MvPolynomial ℝ ℝ)
        (genL κ a b f)) := by
  set Φ : ℝ → ℝ := fun x => lam κ a b (G * Polynomial.aeval (MvPolynomial.X w : MvPolynomial ℝ ℝ)
    (semi κ a b (x - w) f)) with hΦ
  set D : ℝ → ℝ := fun x => lam κ a b (G * Polynomial.aeval (MvPolynomial.X w : MvPolynomial ℝ ℝ)
    (semi κ a b (x - w) (genL κ a b f))) with hD
  have hderΦ : ∀ x, HasDerivAt Φ (D x) x := by
    intro x
    have h1 := (hasDerivAt_lam_semi hκ ha hb G w f (x - w)).comp x
      ((hasDerivAt_id x).sub_const w)
    simp only [mul_one, Function.comp_def, id] at h1
    rw [hD]
    simp only
    rw [semi_genL]
    exact h1
  have hDc : Continuous D := continuous_iff_continuousAt.2 fun x => by
    have h := (hasDerivAt_lam_semi hκ ha hb G w (genL κ a b f) (x - w)).comp x
      ((hasDerivAt_id x).sub_const w)
    simpa [Function.comp_def] using h.continuousAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderΦ x)
    (hDc.intervalIntegrable w v)
  have hΦv : Φ v = lam κ a b (G * Polynomial.aeval (MvPolynomial.X v : MvPolynomial ℝ ℝ) f) :=
    (lam_mul_aeval hκ ha hb hwv hG f).symm
  have hΦw : Φ w = lam κ a b (G * Polynomial.aeval (MvPolynomial.X w : MvPolynomial ℝ ℝ) f) := by
    simp [hΦ]
  rw [← hΦv, ← hΦw, ← hFTC]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hwv] at hx
  exact (lam_mul_aeval hκ ha hb hx.1 hG (genL κ a b f)).symm

variable (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)

/-- **Mixed moments of the constructed process.** -/
theorem integral_prod_mul_eval {m : ℕ} (s : Fin m → ℝ) (k : Fin m → ℕ) (x : ℝ)
    (f : Polynomial ℝ) :
    ∫ ω, (∏ i, jacU κ a b hκ ha hb (s i) ω ^ k i) * f.eval (jacU κ a b hκ ha hb x ω)
      ∂(pathMeasure κ a b hκ ha hb) =
      lam κ a b (prodX s k * Polynomial.aeval (MvPolynomial.X x : MvPolynomial ℝ ℝ) f) := by
  rw [← integral_eval_pathMeasure hκ ha hb]
  refine integral_congr_ae ?_
  have hall : ∀ᵐ ω ∂(pathMeasure κ a b hκ ha hb),
      ∀ i, jacU κ a b hκ ha hb (s i) ω = toConfig ω (s i) :=
    ae_all_iff.2 fun i => jacU_ae_eq hκ ha hb (s i)
  filter_upwards [hall, jacU_ae_eq hκ ha hb x] with ω hω hx
  rw [map_mul, eval_prodX, eval_aeval_X, hx]
  simp only [hω]

theorem gen_pow_eq_eval_genL (n : ℕ) (y : ℝ) :
    Jacobi.gen κ a b (fun z => z ^ n) y = (genL κ a b (Polynomial.X ^ n)).eval y := by
  have h := Jacobi.gen_eval κ a b (Polynomial.X ^ n) y
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [h, eval_genL, Jacobi.genPoly]

/-- Fubini for the time integral. -/
theorem integral_mul_intervalIntegral {m : ℕ} (s : Fin m → ℝ) (k : Fin m → ℕ) {w v : ℝ}
    (hwv : w ≤ v) (q : Polynomial ℝ) :
    ∫ ω, (∏ i, jacU κ a b hκ ha hb (s i) ω ^ k i) *
        (∫ x in w..v, q.eval (jacU κ a b hκ ha hb x ω)) ∂(pathMeasure κ a b hκ ha hb) =
      ∫ x in w..v, ∫ ω, (∏ i, jacU κ a b hκ ha hb (s i) ω ^ k i) *
        q.eval (jacU κ a b hκ ha hb x ω) ∂(pathMeasure κ a b hκ ha hb) := by
  set P := pathMeasure κ a b hκ ha hb
  set U := jacU κ a b hκ ha hb
  set Z : PathSpace → ℝ := fun ω => ∏ i, U (s i) ω ^ k i
  set g : PathSpace → ℝ → ℝ := fun ω x => Z ω * q.eval (U x ω)
  obtain ⟨B, hB⟩ := exists_bound_on_Icc q
  have hUm : Measurable fun p : PathSpace × ℝ => U p.2 p.1 :=
    (measurable_uncurry_of_continuous_of_measurable (fun ω => continuous_jacU hκ ha hb ω)
      (measurable_jacU hκ ha hb)).comp measurable_swap
  have hZm : Measurable Z :=
    Finset.measurable_prod _ fun i _ => (measurable_jacU hκ ha hb (s i)).pow_const _
  have hZb : ∀ ω, |Z ω| ≤ 1 := fun ω => by
    rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (jacU_mem_Icc hκ ha hb _ ω).1 _)]
    exact Finset.prod_le_one₀ (fun i _ => pow_nonneg (jacU_mem_Icc hκ ha hb _ ω).1 _)
      fun i _ => pow_le_one₀ (jacU_mem_Icc hκ ha hb _ ω).1 (jacU_mem_Icc hκ ha hb _ ω).2
  have hgm : Measurable (Function.uncurry g) :=
    (hZm.comp measurable_fst).mul (q.continuous.measurable.comp hUm)
  have hgb : ∀ ω x, |g ω x| ≤ |B| := fun ω x => by
    simp only [g, abs_mul]
    have := (hB _ (jacU_mem_Icc hκ ha hb x ω)).trans (le_abs_self B)
    nlinarith [hZb ω, abs_nonneg (q.eval (U x ω)), abs_nonneg (Z ω)]
  have hint : Integrable (Function.uncurry g) (P.prod (volume.restrict (Ioc w v))) :=
    Integrable.of_bound hgm.aestronglyMeasurable _ (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact hgb p.1 p.2)
  have hswap := integral_integral_swap hint
  rw [intervalIntegral.integral_of_le hwv, ← hswap]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [g, intervalIntegral.integral_of_le hwv, integral_const_mul]
  rfl

/-- **The constructed process solves the Jacobi martingale problem.** -/
theorem isJacobiMP_jacU :
    Jacobi.IsJacobiMP κ a b (pathMeasure κ a b hκ ha hb) (jacU κ a b hκ ha hb) := by
  refine ⟨jacU_mem_Icc hκ ha hb, continuous_jacU hκ ha hb, measurable_jacU hκ ha hb, ?_⟩
  intro m s k n w v hs hwv
  set P := pathMeasure κ a b hκ ha hb
  set U := jacU κ a b hκ ha hb
  set Z : PathSpace → ℝ := fun ω => ∏ i, U (s i) ω ^ k i
  have hG : ∀ d ∈ (prodX s k).vars, d ≤ w := fun d hd => by
    obtain ⟨i, rfl⟩ := vars_prodX s k d hd
    exact hs i
  have hZm : Measurable Z :=
    Finset.measurable_prod _ fun i _ => (measurable_jacU hκ ha hb (s i)).pow_const _
  have hZb : ∀ ω, |Z ω| ≤ 1 := fun ω => by
    rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (jacU_mem_Icc hκ ha hb _ ω).1 _)]
    exact Finset.prod_le_one₀ (fun i _ => pow_nonneg (jacU_mem_Icc hκ ha hb _ ω).1 _)
      fun i _ => pow_le_one₀ (jacU_mem_Icc hκ ha hb _ ω).1 (jacU_mem_Icc hκ ha hb _ ω).2
  have hint_pow : ∀ x : ℝ, Integrable (fun ω => Z ω * U x ω ^ n) P := fun x =>
    Integrable.of_bound ((hZm.mul ((measurable_jacU hκ ha hb x).pow_const n)).aestronglyMeasurable)
      1 (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |U x ω ^ n| ≤ 1 := by
          rw [abs_pow, abs_of_nonneg (jacU_mem_Icc hκ ha hb x ω).1]
          exact pow_le_one₀ (jacU_mem_Icc hκ ha hb x ω).1 (jacU_mem_Icc hκ ha hb x ω).2
        nlinarith [hZb ω, abs_nonneg (U x ω ^ n), abs_nonneg (Z ω)])
  obtain ⟨B, hB⟩ := exists_bound_on_Icc (genL κ a b (Polynomial.X ^ n))
  have hint_gen : Integrable (fun ω => Z ω *
      ∫ x in w..v, Jacobi.gen κ a b (fun y => y ^ n) (U x ω)) P := by
    simp only [gen_pow_eq_eval_genL]
    have hm : Measurable fun ω => ∫ x in w..v, (genL κ a b (Polynomial.X ^ n)).eval (U x ω) := by
      have hUm : Measurable fun p : PathSpace × ℝ => U p.2 p.1 :=
        (measurable_uncurry_of_continuous_of_measurable (fun ω => continuous_jacU hκ ha hb ω)
          (measurable_jacU hκ ha hb)).comp measurable_swap
      have := ((Polynomial.continuous (genL κ a b (Polynomial.X ^ n))).measurable.comp hUm).stronglyMeasurable
      simp only [intervalIntegral.integral_of_le hwv]
      exact (this.integral_prod_right' (ν := volume.restrict (Ioc w v))).measurable
    refine Integrable.of_bound ((hZm.mul hm).aestronglyMeasurable) (|B| * (v - w))
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |∫ x in w..v, (genL κ a b (Polynomial.X ^ n)).eval (U x ω)| ≤ |B| * (v - w) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := w) (b := v) (C := |B|)
        (f := fun x => (genL κ a b (Polynomial.X ^ n)).eval (U x ω)) (fun x _ => by
          rw [Real.norm_eq_abs]
          exact (hB _ (jacU_mem_Icc hκ ha hb x ω)).trans (le_abs_self B))
      rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hwv)] at this
    nlinarith [hZb ω, abs_nonneg (Z ω), abs_nonneg (∫ x in w..v,
      (genL κ a b (Polynomial.X ^ n)).eval (U x ω))]
  have e1 : ∀ x, ∫ ω, Z ω * U x ω ^ n ∂P =
      lam κ a b (prodX s k * Polynomial.aeval (MvPolynomial.X x : MvPolynomial ℝ ℝ)
        (Polynomial.X ^ n)) := fun x => by
    rw [← integral_prod_mul_eval hκ ha hb s k x]
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Z, U]
    rfl
  have e2 : ∫ ω, Z ω * (∫ x in w..v, Jacobi.gen κ a b (fun y => y ^ n) (U x ω)) ∂P =
      ∫ x in w..v, lam κ a b (prodX s k * Polynomial.aeval (MvPolynomial.X x : MvPolynomial ℝ ℝ)
        (genL κ a b (Polynomial.X ^ n))) := by
    simp only [gen_pow_eq_eval_genL]
    rw [integral_mul_intervalIntegral hκ ha hb s k hwv]
    refine intervalIntegral.integral_congr fun x _ => ?_
    exact integral_prod_mul_eval hκ ha hb s k x _
  have hsplit : (fun ω => Z ω * (U v ω ^ n - U w ω ^ n -
      ∫ x in w..v, Jacobi.gen κ a b (fun y => y ^ n) (U x ω))) =
      fun ω => (Z ω * U v ω ^ n - Z ω * U w ω ^ n) -
        Z ω * ∫ x in w..v, Jacobi.gen κ a b (fun y => y ^ n) (U x ω) := by
    funext ω; ring
  show ∫ ω, Z ω * (U v ω ^ n - U w ω ^ n -
      ∫ x in w..v, Jacobi.gen κ a b (fun y => y ^ n) (U x ω)) ∂P = 0
  have hdiff : Integrable (fun ω => Z ω * U v ω ^ n - Z ω * U w ω ^ n) P :=
    (hint_pow v).sub (hint_pow w)
  rw [hsplit, integral_sub hdiff hint_gen,
    integral_sub (hint_pow v) (hint_pow w), e1, e1, e2,
    lam_mul_aeval_sub hκ ha hb hwv hG, sub_self]

end JacobiExists

end Sec2

end InteractingSLE
