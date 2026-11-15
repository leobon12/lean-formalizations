/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Probability.Notation

/-!
# The Jacobi diffusion on `[0, 1]`: the polynomial martingale problem and its moments

Packet PROVE-SEC2-JAC. The Jacobi diffusion of the proof of Theorem 2.2 (Specification p. 22,
`source/spec/p001-048.md` L496–L514) solves
`dU = √((κ/2) U (1 - U)) dβ + ½ {a (1 - U) - b U} du`; its generator is
`L f(x) = (κ/4) x (1 - x) f''(x) + ½ (a (1 - x) - b x) f'(x)` (`gen`).

This file takes the martingale-problem side: a process `U` indexed by all of `ℝ` (the logarithmic
clock runs over `(-∞, ∞)`), with values in `[0, 1]` and continuous paths, such that
`U_v^n - U_w^n - ∫_w^v L(x^n)(U_x) dx` is orthogonal to every product of earlier values
(`IsJacobiMP`). On monomials `L x^n = d_n x^{n-1} + c_n x^n` with `c_n < 0` for `n ≥ 1`
(`gen_pow`), so the moments satisfy a triangular linear system with stable diagonal.

* `moment_eq_jacobiMoment`: **every** such process is stationary with the moments of the beta law
  `Beta(2a/κ, 2b/κ)`: `E U_u^n = m_n`, `m_n = ∏_{k<n} (2a/κ + k)/(2(a+b)/κ + k)`. The
  argument: `M(u) = E U_u^n` is bounded on all of `ℝ` and solves `M' = c_n M + d_n m_{n-1}`, and the
  only bounded solution on `ℝ` of a stable affine equation is its equilibrium. This replaces the
  source's "start the transition kernel at time `u - r` and let `r → ∞`" (L546), and it shows the
  invariance of the beta law on polynomials (L504–L506, divergence-form route) at the same time.
* `mixedMoment_eq`: any two such processes (on any probability spaces) have the same mixed moments
  `E ∏ U_{s_i}^{k_i}` (induction on the number of times, the last time propagated by the
  triangular system from the previous one). Since the values lie in `[0, 1]`, the mixed moments
  determine the finite-dimensional laws.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace InteractingSLE

namespace Sec2

namespace Jacobi

/-- The generator of the Jacobi diffusion,
`L f(x) = (κ/4) x (1 - x) f''(x) + ½ (a (1 - x) - b x) f'(x)`. -/
def gen (κ a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  κ / 4 * (x * (1 - x)) * deriv (deriv f) x + (a * (1 - x) - b * x) / 2 * deriv f x

/-- The coefficient `d_n = (κ/4) n (n - 1) + n a / 2` of `x^{n-1}` in `L x^n`. -/
def dcoef (κ a : ℝ) (n : ℕ) : ℝ := κ / 4 * (n * ((n : ℝ) - 1)) + n * a / 2

/-- The coefficient `c_n = -((κ/4) n (n - 1) + n (a + b) / 2)` of `x^n` in `L x^n`. -/
def ccoef (κ a b : ℝ) (n : ℕ) : ℝ := -(κ / 4 * (n * ((n : ℝ) - 1)) + n * (a + b) / 2)

/-- The moments of `Beta(2a/κ, 2b/κ)`, by the recursion `m_n = d_n m_{n-1} / (-c_n)`. -/
def jacobiMoment (κ a b : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => jacobiMoment κ a b n * (dcoef κ a (n + 1) / -ccoef κ a b (n + 1))

theorem deriv_pow_fun (n : ℕ) : deriv (fun y : ℝ => y ^ n) = fun y => (n : ℝ) * y ^ (n - 1) := by
  funext y
  simp

theorem deriv_deriv_pow_fun (n : ℕ) :
    deriv (deriv fun y : ℝ => y ^ n) = fun y => (n : ℝ) * (((n - 1 : ℕ) : ℝ) * y ^ (n - 1 - 1)) := by
  rw [deriv_pow_fun]
  funext y
  simp

/-- `L x^n = d_n x^{n-1} + c_n x^n`. -/
theorem gen_pow (κ a b : ℝ) (n : ℕ) (x : ℝ) :
    gen κ a b (fun y => y ^ n) x = dcoef κ a n * x ^ (n - 1) + ccoef κ a b n * x ^ n := by
  rw [gen, deriv_deriv_pow_fun, deriv_pow_fun, dcoef, ccoef]
  rcases n with _ | _ | n
  · simp
  · simp only [Nat.cast_one, sub_self, mul_zero, zero_add, Nat.sub_self, pow_zero,
      mul_one, pow_one, one_mul]
    ring
  · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
    ring

theorem ccoef_neg {κ a b : ℝ} (hκ : 0 ≤ κ) (hab : 0 < a + b) {n : ℕ} (hn : 1 ≤ n) :
    ccoef κ a b n < 0 := by
  rw [ccoef, neg_lt_zero]
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : 0 ≤ κ / 4 * (n * ((n : ℝ) - 1)) := by
    apply mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have : 0 < (n : ℝ) * (a + b) / 2 := by positivity
  linarith

/-- The beta moments are the equilibrium of the moment system: `c_n m_n + d_n m_{n-1} = 0`. -/
theorem ccoef_mul_jacobiMoment_add {κ a b : ℝ} (hκ : 0 ≤ κ) (hab : 0 < a + b) (n : ℕ) :
    ccoef κ a b (n + 1) * jacobiMoment κ a b (n + 1) + dcoef κ a (n + 1) * jacobiMoment κ a b n =
      0 := by
  have hc := (ccoef_neg hκ hab (Nat.le_add_left 1 n)).ne
  rw [jacobiMoment]
  generalize ccoef κ a b (n + 1) = c at hc ⊢
  field_simp
  ring

/-- **Affine linear equation in integral form.** If `M` is continuous and
`M x - M w = ∫_w^x (c M + d)` for `x ≥ w`, then `M x + d/c = (M w + d/c) e^{c (x - w)}` for `x ≥ w`. -/
theorem affine_ode_eq {M : ℝ → ℝ} (hM : Continuous M) {c d w : ℝ} (hc : c ≠ 0)
    (hint : ∀ x, w ≤ x → M x - M w = ∫ y in w..x, (c * M y + d)) {x : ℝ} (hx : w ≤ x) :
    M x + d / c = (M w + d / c) * exp (c * (x - w)) := by
  have hg : Continuous fun y => c * M y + d := (hM.const_mul c).add continuous_const
  set F : ℝ → ℝ := fun y => M w + ∫ t in w..y, (c * M t + d) with hFdef
  have hF : ∀ y, HasDerivAt F (c * M y + d) y := fun y =>
    (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt).const_add _
  have hFM : ∀ y, w ≤ y → F y = M y := fun y hy => by
    simp only [hFdef]; linarith [hint y hy]
  set N : ℝ → ℝ := fun y => (F y + d / c) * exp (-(c * (y - w))) with hNdef
  have hN : ∀ y, HasDerivAt N ((c * M y + d) * exp (-(c * (y - w))) +
      (F y + d / c) * (exp (-(c * (y - w))) * -(c * 1))) y := fun y => by
    have h1 : HasDerivAt (fun y => -(c * (y - w))) (-(c * 1)) y :=
      (((hasDerivAt_id y).sub_const w).const_mul c).neg
    exact ((hF y).add_const (d / c)).mul h1.exp
  have hcont : ContinuousOn N (Icc w x) :=
    (continuous_iff_continuousAt.2 fun y => (hN y).continuousAt).continuousOn
  have hconst := constant_of_has_deriv_right_zero hcont (fun y hy => by
    have := (hN y).hasDerivWithinAt (s := Ici y)
    convert this using 1
    rw [← hFM y hy.1]
    field_simp
    ring) x ⟨hx, le_rfl⟩
  simp only [hNdef, sub_self, mul_zero, neg_zero, exp_zero, mul_one] at hconst
  rw [hFM x hx, hFM w le_rfl] at hconst
  have he : exp (c * (x - w)) * exp (-(c * (x - w))) = 1 := by rw [← exp_add]; simp
  calc M x + d / c = (M x + d / c) * exp (-(c * (x - w))) * exp (c * (x - w)) := by
        rw [mul_assoc, mul_comm (exp _), he, mul_one]
    _ = (M w + d / c) * exp (c * (x - w)) := by rw [hconst]

/-- **The only bounded solution on all of `ℝ` of a stable affine equation is its equilibrium**:
if `M` is bounded and continuous on `ℝ`, `c < 0`, and `M x - M w = ∫_w^x (c M + d)` for all
`w ≤ x`, then `M ≡ -d/c`. -/
theorem eq_of_bounded_affine_ode {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hC : ∀ u, |M u| ≤ C)
    {c d : ℝ} (hc : c < 0) (hint : ∀ w x, w ≤ x → M x - M w = ∫ y in w..x, (c * M y + d))
    (x : ℝ) : M x = -d / c := by
  have hbound : ∀ w, w ≤ x → |M x + d / c| ≤ (C + |d / c|) * exp (c * (x - w)) := by
    intro w hw
    rw [affine_ode_eq hM hc.ne (hint w) hw, abs_mul, abs_of_pos (exp_pos _)]
    gcongr
    exact (abs_add_le _ _).trans (by linarith [hC w])
  have hlim : Tendsto (fun w => (C + |d / c|) * exp (c * (x - w))) atBot (𝓝 0) := by
    have h1 : Tendsto (fun w : ℝ => x - w) atBot atTop :=
      tendsto_atBot_atTop.2 fun b => ⟨x - b, fun w hw => by linarith⟩
    have h2 := tendsto_exp_atBot.comp (h1.const_mul_atTop_of_neg hc)
    simpa using h2.const_mul (C + |d / c|)
  have h0 : |M x + d / c| ≤ 0 :=
    ge_of_tendsto hlim ((eventually_le_atBot x).mono fun w hw => hbound w hw)
  have : M x + d / c = 0 := abs_nonpos_iff.1 h0
  rw [neg_div]
  linarith

section Process

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The martingale problem of the Jacobi generator on polynomials**, for a process indexed by all
of `ℝ`: values in `[0, 1]`, continuous paths, measurable coordinates, and for all `w ≤ v` and
`n`, `U_v^n - U_w^n - ∫_w^v L(x^n)(U_x) dx` is orthogonal to every product `∏ U_{s_i}^{k_i}` of
values at earlier times `s_i ≤ w`. -/
def IsJacobiMP (κ a b : ℝ) (P : Measure Ω) (U : ℝ → Ω → ℝ) : Prop :=
  (∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) ∧ (∀ ω, Continuous fun u => U u ω) ∧ (∀ u, Measurable (U u)) ∧
    ∀ (m : ℕ) (s : Fin m → ℝ) (k : Fin m → ℕ) (n : ℕ) (w v : ℝ), (∀ i, s i ≤ w) → w ≤ v →
      ∫ ω, (∏ i, U (s i) ω ^ k i) *
        (U v ω ^ n - U w ω ^ n - ∫ x in w..v, gen κ a b (fun y => y ^ n) (U x ω)) ∂P = 0

/-- The product `∏ U_{s_i}^{k_i}`. -/
def prodPow (U : ℝ → Ω → ℝ) {m : ℕ} (s : Fin m → ℝ) (k : Fin m → ℕ) (ω : Ω) : ℝ :=
  ∏ i, U (s i) ω ^ k i

omit [MeasurableSpace Ω] in
theorem prodPow_add_single (U : ℝ → Ω → ℝ) {m : ℕ} (s : Fin m → ℝ) (k : Fin m → ℕ) (i₀ : Fin m)
    (n : ℕ) (ω : Ω) :
    prodPow U s (fun i => k i + if i = i₀ then n else 0) ω = prodPow U s k ω * U (s i₀) ω ^ n := by
  simp only [prodPow, pow_add, Finset.prod_mul_distrib, pow_ite, pow_zero]
  rw [Finset.prod_ite_eq' Finset.univ i₀]
  simp

variable {κ a b : ℝ} {P : Measure Ω} {U : ℝ → Ω → ℝ}

theorem IsJacobiMP.mem_Icc (hU : IsJacobiMP κ a b P U) (u : ℝ) (ω : Ω) : U u ω ∈ Icc (0 : ℝ) 1 :=
  hU.1 u ω

theorem IsJacobiMP.continuous (hU : IsJacobiMP κ a b P U) (ω : Ω) : Continuous fun u => U u ω :=
  hU.2.1 ω

theorem IsJacobiMP.measurable (hU : IsJacobiMP κ a b P U) (u : ℝ) : Measurable (U u) :=
  hU.2.2.1 u

theorem IsJacobiMP.measurable_uncurry (hU : IsJacobiMP κ a b P U) :
    Measurable fun p : Ω × ℝ => U p.2 p.1 :=
  (measurable_uncurry_of_continuous_of_measurable hU.continuous hU.measurable).comp measurable_swap

theorem IsJacobiMP.pow_mem_Icc (hU : IsJacobiMP κ a b P U) (u : ℝ) (ω : Ω) (n : ℕ) :
    U u ω ^ n ∈ Icc (0 : ℝ) 1 :=
  ⟨pow_nonneg (hU.mem_Icc u ω).1 n, pow_le_one₀ (hU.mem_Icc u ω).1 (hU.mem_Icc u ω).2⟩

theorem IsJacobiMP.prodPow_mem_Icc (hU : IsJacobiMP κ a b P U) {m : ℕ} (s : Fin m → ℝ)
    (k : Fin m → ℕ) (ω : Ω) : prodPow U s k ω ∈ Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (hU.pow_mem_Icc _ _ _).1,
    Finset.prod_le_one₀ (fun _ _ => (hU.pow_mem_Icc _ _ _).1) fun _ _ => (hU.pow_mem_Icc _ _ _).2⟩

theorem IsJacobiMP.measurable_prodPow (hU : IsJacobiMP κ a b P U) {m : ℕ} (s : Fin m → ℝ)
    (k : Fin m → ℕ) : Measurable (prodPow U s k) :=
  Finset.measurable_prod _ fun i _ => (hU.measurable (s i)).pow_const _

theorem abs_le_one_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : |x| ≤ 1 := by
  rw [abs_of_nonneg hx.1]; exact hx.2

theorem abs_mul_abs_le_one {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x| * |y| ≤ 1 := by
  nlinarith [abs_nonneg x, abs_nonneg y]

variable [IsProbabilityMeasure P]

/-- The moment function `x ↦ E[Z U_x^n]`, `Z = ∏ U_{s_i}^{k_i}`. -/
def momF (P : Measure Ω) (U : ℝ → Ω → ℝ) {m : ℕ} (s : Fin m → ℝ) (k : Fin m → ℕ) (n : ℕ)
    (x : ℝ) : ℝ :=
  ∫ ω, prodPow U s k ω * U x ω ^ n ∂P

theorem IsJacobiMP.integrable_prodPow_mul (hU : IsJacobiMP κ a b P U) {m : ℕ} (s : Fin m → ℝ)
    (k : Fin m → ℕ) (n : ℕ) (x : ℝ) : Integrable (fun ω => prodPow U s k ω * U x ω ^ n) P := by
  refine Integrable.of_bound (((hU.measurable_prodPow s k).mul
    ((hU.measurable x).pow_const n)).aestronglyMeasurable) 1 (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact abs_mul_abs_le_one (abs_le_one_of_mem_Icc (hU.prodPow_mem_Icc s k ω))
    (abs_le_one_of_mem_Icc (hU.pow_mem_Icc x ω n))

theorem IsJacobiMP.abs_momF_le (hU : IsJacobiMP κ a b P U) {m : ℕ} (s : Fin m → ℝ)
    (k : Fin m → ℕ) (n : ℕ) (x : ℝ) : |momF P U s k n x| ≤ 1 := by
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ω, |prodPow U s k ω * U x ω ^ n| ∂P ≤ ∫ _ω, (1 : ℝ) ∂P := by
        refine integral_mono (hU.integrable_prodPow_mul s k n x).abs (integrable_const _) fun ω => ?_
        rw [abs_mul]
        exact abs_mul_abs_le_one (abs_le_one_of_mem_Icc (hU.prodPow_mem_Icc s k ω))
          (abs_le_one_of_mem_Icc (hU.pow_mem_Icc x ω n))
    _ = 1 := by simp

theorem IsJacobiMP.continuous_momF (hU : IsJacobiMP κ a b P U) {m : ℕ} (s : Fin m → ℝ)
    (k : Fin m → ℕ) (n : ℕ) : Continuous (momF P U s k n) := by
  refine continuous_of_dominated (bound := fun _ => 1)
    (fun x => (hU.integrable_prodPow_mul s k n x).aestronglyMeasurable)
    (fun x => ae_of_all _ fun ω => ?_) (integrable_const _)
    (ae_of_all _ fun ω => continuous_const.mul ((hU.continuous ω).pow n))
  rw [Real.norm_eq_abs, abs_mul]
  exact abs_mul_abs_le_one (abs_le_one_of_mem_Icc (hU.prodPow_mem_Icc s k ω))
    (abs_le_one_of_mem_Icc (hU.pow_mem_Icc x ω n))

/-- **The moment system.** For `Z = ∏ U_{s_i}^{k_i}` with all `s_i ≤ w` and `w ≤ x`:
`E[Z U_x^n] - E[Z U_w^n] = ∫_w^x (c_n E[Z U_y^n] + d_n E[Z U_y^{n-1}]) dy`. -/
theorem IsJacobiMP.momF_sub (hU : IsJacobiMP κ a b P U) {m : ℕ} (s : Fin m → ℝ) (k : Fin m → ℕ)
    (n : ℕ) {w x : ℝ} (hs : ∀ i, s i ≤ w) (hwx : w ≤ x) :
    momF P U s k n x - momF P U s k n w =
      ∫ y in w..x, (ccoef κ a b n * momF P U s k n y + dcoef κ a n * momF P U s k (n - 1) y) := by
  have hmp : ∫ ω, prodPow U s k ω * (U x ω ^ n - U w ω ^ n -
      ∫ y in w..x, gen κ a b (fun z => z ^ n) (U y ω)) ∂P = 0 := hU.2.2.2 m s k n w x hs hwx
  set g : Ω → ℝ → ℝ := fun ω y => prodPow U s k ω * gen κ a b (fun z => z ^ n) (U y ω)
  have hgm : Measurable (Function.uncurry g) := by
    have h1 : Measurable fun p : Ω × ℝ => prodPow U s k p.1 :=
      (hU.measurable_prodPow s k).comp measurable_fst
    have h2 : Measurable fun p : Ω × ℝ => U p.2 p.1 := hU.measurable_uncurry
    simp only [g, gen_pow]
    exact h1.mul (((h2.pow_const _).const_mul _).add ((h2.pow_const _).const_mul _))
  have hgb : ∀ ω y, |g ω y| ≤ |dcoef κ a n| + |ccoef κ a b n| := fun ω y => by
    simp only [g, gen_pow, abs_mul]
    have h1 := abs_le_one_of_mem_Icc (hU.prodPow_mem_Icc s k ω)
    have h2 := abs_le_one_of_mem_Icc (hU.pow_mem_Icc y ω (n - 1))
    have h3 := abs_le_one_of_mem_Icc (hU.pow_mem_Icc y ω n)
    calc |prodPow U s k ω| * |dcoef κ a n * U y ω ^ (n - 1) + ccoef κ a b n * U y ω ^ n|
        ≤ 1 * (|dcoef κ a n| * 1 + |ccoef κ a b n| * 1) := by
          gcongr
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
          gcongr
      _ = _ := by ring
  have hint : Integrable (Function.uncurry g) (P.prod (volume.restrict (Ioc w x))) :=
    Integrable.of_bound hgm.aestronglyMeasurable _ (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact hgb p.1 p.2)
  have hswap := integral_integral_swap hint
  have hin : ∀ ω, IntervalIntegrable (fun y => gen κ a b (fun z => z ^ n) (U y ω)) volume w x :=
    fun ω => by
      simp only [gen_pow]
      exact (((hU.continuous ω).pow _).const_mul _ |>.add (((hU.continuous ω).pow _).const_mul _)
        )|>.intervalIntegrable _ _
  have hZint : Integrable (fun ω => prodPow U s k ω * ∫ y in w..x,
      gen κ a b (fun z => z ^ n) (U y ω)) P := by
    have : (fun ω => prodPow U s k ω * ∫ y in w..x, gen κ a b (fun z => z ^ n) (U y ω)) =
        fun ω => ∫ y in Ioc w x, g ω y := by
      funext ω
      simp only [g, intervalIntegral.integral_of_le hwx, integral_const_mul]
    rw [this]
    exact hint.integral_prod_left
  have h1 := hU.integrable_prodPow_mul s k n x
  have h2 := hU.integrable_prodPow_mul s k n w
  have h12 : Integrable (fun ω => prodPow U s k ω * U x ω ^ n - prodPow U s k ω * U w ω ^ n) P :=
    h1.sub h2
  simp only [mul_sub] at hmp
  rw [integral_sub h12 hZint, integral_sub h1 h2, sub_eq_zero] at hmp
  rw [momF, momF, hmp]
  have hR : ∫ ω, prodPow U s k ω * (∫ y in w..x, gen κ a b (fun z => z ^ n) (U y ω)) ∂P =
      ∫ y in Ioc w x, ∫ ω, g ω y ∂P := by
    rw [← hswap]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [g, intervalIntegral.integral_of_le hwx, integral_const_mul]
  rw [hR, intervalIntegral.integral_of_le hwx]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  have e1 : ∫ ω, prodPow U s k ω * (dcoef κ a n * U y ω ^ (n - 1)) ∂P =
      dcoef κ a n * ∫ ω, prodPow U s k ω * U y ω ^ (n - 1) ∂P := by
    rw [← integral_const_mul]; congr 1; funext ω; ring
  have e2 : ∫ ω, prodPow U s k ω * (ccoef κ a b n * U y ω ^ n) ∂P =
      ccoef κ a b n * ∫ ω, prodPow U s k ω * U y ω ^ n ∂P := by
    rw [← integral_const_mul]; congr 1; funext ω; ring
  have i1 : Integrable (fun ω => prodPow U s k ω * (dcoef κ a n * U y ω ^ (n - 1))) P :=
    ((hU.integrable_prodPow_mul s k (n - 1) y).const_mul (dcoef κ a n)).congr
      (ae_of_all _ fun ω => by ring)
  have i2 : Integrable (fun ω => prodPow U s k ω * (ccoef κ a b n * U y ω ^ n)) P :=
    ((hU.integrable_prodPow_mul s k n y).const_mul (ccoef κ a b n)).congr
      (ae_of_all _ fun ω => by ring)
  simp only [g, gen_pow, momF, mul_add]
  rw [integral_add i1 i2, e1, e2]
  ring

omit [IsProbabilityMeasure P] in
theorem momF_elim0 (n : ℕ) (x : ℝ) :
    momF P U (Fin.elim0 : Fin 0 → ℝ) Fin.elim0 n x = ∫ ω, U x ω ^ n ∂P := by
  simp [momF, prodPow]

/-- **The process is stationary with the beta moments** (invariance and uniqueness of the
invariant law, Specification p. 22–23, L504–L514, and stationarity of the logarithmic-clock
process, L546): `E U_u^n = m_n = ∏_{k<n} (2a/κ + k)/(2(a+b)/κ + k)` for every `u ∈ ℝ`. -/
theorem IsJacobiMP.moment_eq (hU : IsJacobiMP κ a b P U) (hκ : 0 ≤ κ) (hab : 0 < a + b)
    (n : ℕ) (u : ℝ) : ∫ ω, U u ω ^ n ∂P = jacobiMoment κ a b n := by
  induction n generalizing u with
  | zero => simp [jacobiMoment]
  | succ n ih =>
    have hc := ccoef_neg hκ hab (Nat.le_add_left 1 n)
    have key := eq_of_bounded_affine_ode (hU.continuous_momF Fin.elim0 Fin.elim0 (n + 1))
      (hU.abs_momF_le Fin.elim0 Fin.elim0 (n + 1)) hc
      (d := dcoef κ a (n + 1) * jacobiMoment κ a b n) (fun w x hwx => ?_) u
    · rw [← momF_elim0, key, eq_comm, eq_div_iff hc.ne]
      linarith [ccoef_mul_jacobiMoment_add hκ hab n]
    · rw [hU.momF_sub Fin.elim0 Fin.elim0 (n + 1) (fun i => i.elim0) hwx]
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [Nat.add_sub_cancel]
      rw [momF_elim0 (U := U) n y, ih]

/-- **All mixed moments agree** for any two solutions of the Jacobi martingale problem on `ℝ` with
the same parameters (on any probability spaces): `E ∏ U_{s_i}^{k_i} = E' ∏ U'_{s_i}^{k_i}`.
Hence (values in `[0, 1]`) their finite-dimensional laws agree: the law of the stationary process
is unique (Specification p. 24, L546, "The Markov transition kernels then force all its
finite-dimensional laws to agree with those of the two-sided stationary diffusion"). -/
theorem IsJacobiMP.integral_prodPow_eq {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {U' : ℝ → Ω' → ℝ} (hU : IsJacobiMP κ a b P U)
    (hU' : IsJacobiMP κ a b P' U') (hκ : 0 ≤ κ) (hab : 0 < a + b) :
    ∀ (m : ℕ) (s : Fin m → ℝ) (k : Fin m → ℕ),
      ∫ ω, prodPow U s k ω ∂P = ∫ ω, prodPow U' s k ω ∂P' := by
  intro m
  induction m with
  | zero => intro s k; simp [prodPow]
  | succ m ih =>
    intro s k
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ s Finset.univ_nonempty
    have hsplit : ∀ ω, prodPow U s k ω =
        prodPow U (s ∘ j.succAbove) (k ∘ j.succAbove) ω * U (s j) ω ^ k j := fun ω => by
      simp only [prodPow, Fin.prod_univ_succAbove _ j, Function.comp_apply]; ring
    have hsplit' : ∀ ω, prodPow U' s k ω =
        prodPow U' (s ∘ j.succAbove) (k ∘ j.succAbove) ω * U' (s j) ω ^ k j := fun ω => by
      simp only [prodPow, Fin.prod_univ_succAbove _ j, Function.comp_apply]; ring
    simp only [hsplit, hsplit']
    set s' := s ∘ j.succAbove with hs'
    set k' := k ∘ j.succAbove
    have hs'v : ∀ i, s' i ≤ s j := fun i => hj _ (Finset.mem_univ _)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have e : ∀ ω, prodPow U s' k' ω = 1 := fun ω => by simp [prodPow]
      have e' : ∀ ω, prodPow U' s' k' ω = 1 := fun ω => by simp [prodPow]
      simp only [e, e', one_mul]
      rw [hU.moment_eq hκ hab, hU'.moment_eq hκ hab]
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ s'
      (Finset.univ_nonempty_iff.2 ⟨⟨0, hm⟩⟩)
    have hs'w : ∀ i, s' i ≤ s' i₀ := fun i => hi₀ _ (Finset.mem_univ _)
    have key : ∀ n x, s' i₀ ≤ x → momF P U s' k' n x = momF P' U' s' k' n x := by
      intro n
      induction n with
      | zero =>
        intro x _
        simp only [momF, pow_zero, mul_one]
        exact ih s' k'
      | succ n ihn =>
        intro x hx
        set D : ℝ → ℝ := fun y => momF P U s' k' (n + 1) y - momF P' U' s' k' (n + 1) y with hD
        have hDc : Continuous D :=
          (hU.continuous_momF s' k' (n + 1)).sub (hU'.continuous_momF s' k' (n + 1))
        have hDw : D (s' i₀) = 0 := by
          simp only [hD, momF]
          rw [sub_eq_zero]
          have h1 := ih s' (fun i => k' i + if i = i₀ then n + 1 else 0)
          simp only [prodPow_add_single] at h1
          exact h1
        have hc := ccoef_neg hκ hab (Nat.le_add_left 1 n)
        have hode : ∀ x, s' i₀ ≤ x → D x - D (s' i₀) =
            ∫ y in (s' i₀)..x, (ccoef κ a b (n + 1) * D y + 0) := by
          intro x hx
          have e1 := hU.momF_sub s' k' (n + 1) hs'w hx
          have e2 := hU'.momF_sub s' k' (n + 1) hs'w hx
          have hi : IntervalIntegrable (fun y => ccoef κ a b (n + 1) * momF P U s' k' (n + 1) y +
              dcoef κ a (n + 1) * momF P U s' k' (n + 1 - 1) y) volume (s' i₀) x :=
            (((hU.continuous_momF s' k' (n + 1)).const_mul _).add
              ((hU.continuous_momF s' k' _).const_mul _)).intervalIntegrable _ _
          have hi' : IntervalIntegrable (fun y => ccoef κ a b (n + 1) * momF P' U' s' k' (n + 1) y +
              dcoef κ a (n + 1) * momF P' U' s' k' (n + 1 - 1) y) volume (s' i₀) x :=
            (((hU'.continuous_momF s' k' (n + 1)).const_mul _).add
              ((hU'.continuous_momF s' k' _).const_mul _)).intervalIntegrable _ _
          calc D x - D (s' i₀) = (momF P U s' k' (n + 1) x - momF P U s' k' (n + 1) (s' i₀)) -
                (momF P' U' s' k' (n + 1) x - momF P' U' s' k' (n + 1) (s' i₀)) := by
                simp only [hD]; ring
            _ = _ := by
                rw [e1, e2, ← intervalIntegral.integral_sub hi hi']
                refine intervalIntegral.integral_congr fun y hy => ?_
                rw [uIcc_of_le hx] at hy
                simp only [Nat.add_sub_cancel, hD, ihn y hy.1]
                ring
        have := affine_ode_eq hDc hc.ne hode hx
        rw [hDw, zero_div, add_zero, add_zero, zero_mul] at this
        exact sub_eq_zero.1 this
    exact key (k j) (s j) (hs'v i₀)

end Process

end Jacobi

end Sec2

end InteractingSLE
