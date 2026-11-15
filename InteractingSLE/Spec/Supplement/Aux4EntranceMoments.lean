/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiMoments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Aux. lemma 4, I: uniform moment estimates for the Jacobi martingale problem

Packet PROVE-T14-DS3. Specification, Aux. lemma 4 (`source/spec/p001-048.md` L653–L700, pp. 28–30): "Its invariant
laws `Beta(2a_n/κ, 2b_n/κ)` converge to the limiting beta law. On every bounded interval of logarithmic time the drifts
are uniformly bounded and the diffusion coefficient is the same bounded continuous function. The fourth-moment estimate
… gives `E|U_v^{(n)} − U_u^{(n)}|⁴ ≤ C(|v − u|² + |v − u|⁴)`. … weak uniqueness for the Jacobi equation, with the
limiting invariant initial law, identifies that limit."

For every solution `U` of the landed polynomial martingale problem `Sec2.Jacobi.IsJacobiMP κ a b P U`:

* `jmp_integral_mul_pow_sub`: `E[U_w^j (U_x^n − U_w^n)] = E[U_w^j ∫_w^x L(y^n)(U_y) dy]` (`w ≤ x`);
* `jmp_integral_sq_sub_le`: `E (U_v − U_w)² ≤ (κ/8 + a + b)(v − w)`;
* **`jmp_integral_pow_four_sub_le`**: `E (U_v − U_w)⁴ ≤ quartC κ a b · (v − w)²` with the explicit constant
  `quartC κ a b = (3κ/4 + 2(a + b))(κ/8 + a + b)/2`, continuous in the parameters (so uniform on parameter
  neighbourhoods, unlike the landed existential bound for the constructed process);
* **`tendsto_integral_prodPow`**: if `U^{(m)}` solve the martingale problem with parameters `(κ, a_m, b_m)` and `U` with
  `(κ, a, b)`, and `a_m → a`, `b_m → b`, then every mixed moment converges:
  `E ∏ U^{(m)}_{s_i}^{k_i} → E ∏ U_{s_i}^{k_i}`. The proof follows the landed uniqueness proof
  (`IsJacobiMP.integral_prodPow_eq`: induction on the number of times, the largest time split off, induction on its
  exponent through the moment system `IsJacobiMP.momF_sub`), with the uniqueness of the linear ODE replaced by
  Grönwall's inequality, and the one-time moments by the beta moments `jacobiMoment`, which are continuous in the
  parameters.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace InteractingSLE

namespace Supp12

namespace Aux4

open Sec2.Jacobi

section Quartic

variable {Ω : Type*} [MeasurableSpace Ω] {κ a b : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {U : ℝ → Ω → ℝ}

/-- The constant of the fourth-moment bound. -/
def quartC (κ a b : ℝ) : ℝ := (3 * κ / 4 + 2 * (a + b)) * (κ / 8 + (a + b)) / 2

theorem continuous_quartC (κ : ℝ) : Continuous fun p : ℝ × ℝ => quartC κ p.1 p.2 := by
  unfold quartC; fun_prop

/-- The martingale-problem integral `∫_w^x L(y^n)(U_y) dy` along one path. -/
def genInt (κ a b : ℝ) (U : ℝ → Ω → ℝ) (n : ℕ) (w x : ℝ) (ω : Ω) : ℝ :=
  ∫ y in w..x, (dcoef κ a n * U y ω ^ (n - 1) + ccoef κ a b n * U y ω ^ n)

omit [IsProbabilityMeasure P] in
theorem jmp_genInt_eq (_hU : IsJacobiMP κ a b P U) (n : ℕ) (w x : ℝ) (ω : Ω) :
    ∫ y in w..x, gen κ a b (fun z => z ^ n) (U y ω) = genInt κ a b U n w x ω := by
  simp only [genInt, gen_pow]

omit [IsProbabilityMeasure P] in
theorem jmp_intervalIntegrable_gen (hU : IsJacobiMP κ a b P U) (n : ℕ) (w x : ℝ) (ω : Ω) :
    IntervalIntegrable (fun y => dcoef κ a n * U y ω ^ (n - 1) + ccoef κ a b n * U y ω ^ n) volume w x :=
  ((((hU.continuous ω).pow _).const_mul _).add (((hU.continuous ω).pow _).const_mul _)).intervalIntegrable _ _

omit [IsProbabilityMeasure P] in
theorem jmp_measurable_genInt (hU : IsJacobiMP κ a b P U) (n : ℕ) {w x : ℝ} (hwx : w ≤ x) :
    Measurable (genInt κ a b U n w x) := by
  have h2 : Measurable fun p : Ω × ℝ => U p.2 p.1 := hU.measurable_uncurry
  have hm : Measurable fun p : Ω × ℝ => dcoef κ a n * U p.2 p.1 ^ (n - 1) + ccoef κ a b n * U p.2 p.1 ^ n :=
    ((h2.pow_const _).const_mul _).add ((h2.pow_const _).const_mul _)
  have : genInt κ a b U n w x = fun ω => ∫ y in Ioc w x,
      (dcoef κ a n * U y ω ^ (n - 1) + ccoef κ a b n * U y ω ^ n) := by
    funext ω; simp only [genInt, intervalIntegral.integral_of_le hwx]
  rw [this]
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc w x))
    (f := fun p : Ω × ℝ => dcoef κ a n * U p.2 p.1 ^ (n - 1) + ccoef κ a b n * U p.2 p.1 ^ n)).measurable

omit [IsProbabilityMeasure P] in
theorem jmp_abs_gen_le (hU : IsJacobiMP κ a b P U) (n : ℕ) (y : ℝ) (ω : Ω) :
    |dcoef κ a n * U y ω ^ (n - 1) + ccoef κ a b n * U y ω ^ n| ≤ |dcoef κ a n| + |ccoef κ a b n| := by
  have h2 := abs_le_one_of_mem_Icc (hU.pow_mem_Icc y ω (n - 1))
  have h3 := abs_le_one_of_mem_Icc (hU.pow_mem_Icc y ω n)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  gcongr
  · exact mul_le_of_le_one_right (abs_nonneg _) h2
  · exact mul_le_of_le_one_right (abs_nonneg _) h3

omit [IsProbabilityMeasure P] in
theorem jmp_abs_genInt_le (hU : IsJacobiMP κ a b P U) (n : ℕ) {w x : ℝ} (hwx : w ≤ x) (ω : Ω) :
    |genInt κ a b U n w x ω| ≤ (|dcoef κ a n| + |ccoef κ a b n|) * (x - w) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := w) (b := x)
    (f := fun y => dcoef κ a n * U y ω ^ (n - 1) + ccoef κ a b n * U y ω ^ n)
    (C := |dcoef κ a n| + |ccoef κ a b n|) (fun y _ => by
      rw [Real.norm_eq_abs]; exact jmp_abs_gen_le hU n y ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hwx)] at this
  simpa only [genInt, mul_comm] using this

theorem jmp_integrable_pow_mul_genInt (hU : IsJacobiMP κ a b P U) (j n : ℕ) {w x : ℝ}
    (hwx : w ≤ x) : Integrable (fun ω => U w ω ^ j * genInt κ a b U n w x ω) P := by
  refine Integrable.of_bound (((hU.measurable w).pow_const j).mul
    (jmp_measurable_genInt hU n hwx)).aestronglyMeasurable
    ((|dcoef κ a n| + |ccoef κ a b n|) * (x - w)) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := abs_le_one_of_mem_Icc (hU.pow_mem_Icc w ω j)
  calc |U w ω ^ j| * |genInt κ a b U n w x ω| ≤ 1 * ((|dcoef κ a n| + |ccoef κ a b n|) * (x - w)) :=
        mul_le_mul h1 (jmp_abs_genInt_le hU n hwx ω) (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem jmp_integrable_pow_mul_pow (hU : IsJacobiMP κ a b P U) (j n : ℕ) (w x : ℝ) :
    Integrable (fun ω => U w ω ^ j * U x ω ^ n) P := by
  refine Integrable.of_bound (((hU.measurable w).pow_const j).mul
    ((hU.measurable x).pow_const n)).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact abs_mul_abs_le_one (abs_le_one_of_mem_Icc (hU.pow_mem_Icc w ω j))
    (abs_le_one_of_mem_Icc (hU.pow_mem_Icc x ω n))

/-- **The martingale problem with one earlier time.** -/
theorem jmp_integral_mul_pow_sub (hU : IsJacobiMP κ a b P U) (j n : ℕ) {w x : ℝ}
    (hwx : w ≤ x) :
    ∫ ω, U w ω ^ j * (U x ω ^ n - U w ω ^ n) ∂P = ∫ ω, U w ω ^ j * genInt κ a b U n w x ω ∂P := by
  have hmp := hU.2.2.2 1 (fun _ => w) (fun _ => j) n w x (fun _ => le_rfl) hwx
  simp only [Fin.prod_univ_one, jmp_genInt_eq hU] at hmp
  have h1 : Integrable (fun ω => U w ω ^ j * (U x ω ^ n - U w ω ^ n)) P :=
    ((jmp_integrable_pow_mul_pow hU j n w x).sub (jmp_integrable_pow_mul_pow hU j n w w)).congr
      (ae_of_all _ fun ω => by simp only [Pi.sub_apply]; ring)
  have e : (fun ω => U w ω ^ j * (U x ω ^ n - U w ω ^ n - genInt κ a b U n w x ω)) =
      fun ω => U w ω ^ j * (U x ω ^ n - U w ω ^ n) - U w ω ^ j * genInt κ a b U n w x ω := by
    funext ω; ring
  rw [e, integral_sub h1 (jmp_integrable_pow_mul_genInt hU j n hwx), sub_eq_zero] at hmp
  exact hmp

/-- An interval integral of a continuous function bounded above by `C`. -/
theorem intervalIntegral_le_mul_of_le {f : ℝ → ℝ} (hf : Continuous f) {w v C : ℝ} (hwv : w ≤ v)
    (h : ∀ y ∈ Icc w v, f y ≤ C) : ∫ y in w..v, f y ≤ C * (v - w) := by
  have := intervalIntegral.integral_mono_on hwv (hf.intervalIntegrable w v)
    (intervalIntegrable_const (μ := volume) (c := C)) h
  rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this

/-- The integrand of the second-moment identity. -/
def q2 (κ a b y x : ℝ) : ℝ := κ / 2 * (x * (1 - x)) + (a * (1 - x) - b * x) * (x - y)

theorem q2_le (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : q2 κ a b y x ≤ κ / 8 + (a + b) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have h1 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have h2 : |a * (1 - x) - b * x| ≤ a + b := by
    rw [abs_le]; constructor <;> nlinarith
  have h3 : |x - y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have h4 : (a * (1 - x) - b * x) * (x - y) ≤ a + b := by
    calc (a * (1 - x) - b * x) * (x - y) ≤ |(a * (1 - x) - b * x) * (x - y)| := le_abs_self _
      _ = |a * (1 - x) - b * x| * |x - y| := abs_mul _ _
      _ ≤ (a + b) * 1 := mul_le_mul h2 h3 (abs_nonneg _) (by linarith)
      _ = a + b := mul_one _
  unfold q2
  nlinarith

/-- **Second moment of an increment.** -/
theorem jmp_integral_sq_sub_le (hU : IsJacobiMP κ a b P U) (hκ : 0 ≤ κ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) {w v : ℝ} (hwv : w ≤ v) :
    ∫ ω, (U v ω - U w ω) ^ 2 ∂P ≤ (κ / 8 + (a + b)) * (v - w) := by
  have e1 := jmp_integral_mul_pow_sub hU 0 2 hwv
  have e2 := jmp_integral_mul_pow_sub hU 1 1 hwv
  have i1 : Integrable (fun ω => U w ω ^ 0 * (U v ω ^ 2 - U w ω ^ 2)) P :=
    ((jmp_integrable_pow_mul_pow hU 0 2 w v).sub (jmp_integrable_pow_mul_pow hU 0 2 w w)).congr
      (ae_of_all _ fun ω => by simp only [Pi.sub_apply]; ring)
  have i2 : Integrable (fun ω => U w ω ^ 1 * (U v ω ^ 1 - U w ω ^ 1)) P :=
    ((jmp_integrable_pow_mul_pow hU 1 1 w v).sub (jmp_integrable_pow_mul_pow hU 1 1 w w)).congr
      (ae_of_all _ fun ω => by simp only [Pi.sub_apply]; ring)
  have hsplit : ∫ ω, (U v ω - U w ω) ^ 2 ∂P = ∫ ω, U w ω ^ 0 * (U v ω ^ 2 - U w ω ^ 2) ∂P -
      2 * ∫ ω, U w ω ^ 1 * (U v ω ^ 1 - U w ω ^ 1) ∂P := by
    rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul 2)]
    congr 1; funext ω; ring
  rw [hsplit, e1, e2, ← integral_const_mul,
    ← integral_sub (jmp_integrable_pow_mul_genInt hU 0 2 hwv) ((jmp_integrable_pow_mul_genInt hU 1 1 hwv).const_mul 2)]
  -- pointwise bound
  have hpt : ∀ ω, U w ω ^ 0 * genInt κ a b U 2 w v ω - 2 * (U w ω ^ 1 * genInt κ a b U 1 w v ω) ≤
      (κ / 8 + (a + b)) * (v - w) := fun ω => by
    have hrw : U w ω ^ 0 * genInt κ a b U 2 w v ω - 2 * (U w ω ^ 1 * genInt κ a b U 1 w v ω) =
        ∫ y in w..v, q2 κ a b (U w ω) (U y ω) := by
      have e : (fun y => q2 κ a b (U w ω) (U y ω)) = fun y =>
          (dcoef κ a 2 * U y ω ^ (2 - 1) + ccoef κ a b 2 * U y ω ^ 2) -
            2 * (U w ω * (dcoef κ a 1 * U y ω ^ (1 - 1) + ccoef κ a b 1 * U y ω ^ 1)) := by
        funext y; simp only [q2, dcoef, ccoef]; norm_num; ring
      rw [e, intervalIntegral.integral_sub (jmp_intervalIntegrable_gen hU 2 w v ω)
        (((jmp_intervalIntegrable_gen hU 1 w v ω).const_mul _).const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      simp only [genInt, pow_zero, one_mul, pow_one]
    rw [hrw]
    have hc := hU.continuous ω
    have hcq : Continuous fun y => q2 κ a b (U w ω) (U y ω) := by unfold q2; fun_prop
    exact intervalIntegral_le_mul_of_le hcq hwv fun y _ => q2_le hκ ha hb (hU.mem_Icc y ω) (hU.mem_Icc w ω)
  calc ∫ ω, (U w ω ^ 0 * genInt κ a b U 2 w v ω - 2 * (U w ω ^ 1 * genInt κ a b U 1 w v ω)) ∂P
      ≤ ∫ _ω, (κ / 8 + (a + b)) * (v - w) ∂P :=
        integral_mono ((jmp_integrable_pow_mul_genInt hU 0 2 hwv).sub
          ((jmp_integrable_pow_mul_genInt hU 1 1 hwv).const_mul 2)) (integrable_const _) hpt
    _ = (κ / 8 + (a + b)) * (v - w) := by simp

omit [IsProbabilityMeasure P] in
/-- Linearity of the integral for a combination of four integrable functions. -/
theorem integral_comb4 {f₁ f₂ f₃ f₄ : Ω → ℝ} (h₁ : Integrable f₁ P) (h₂ : Integrable f₂ P)
    (h₃ : Integrable f₃ P) (h₄ : Integrable f₄ P) (c₁ c₂ c₃ : ℝ) :
    ∫ ω, (c₁ * f₁ ω + c₂ * f₂ ω - c₃ * f₃ ω + f₄ ω) ∂P =
      c₁ * ∫ ω, f₁ ω ∂P + c₂ * ∫ ω, f₂ ω ∂P - c₃ * ∫ ω, f₃ ω ∂P + ∫ ω, f₄ ω ∂P := by
  have hA : Integrable (fun ω => c₁ * f₁ ω + c₂ * f₂ ω - c₃ * f₃ ω) P :=
    ((h₁.const_mul c₁).add (h₂.const_mul c₂)).sub (h₃.const_mul c₃)
  have hB : Integrable (fun ω => c₁ * f₁ ω + c₂ * f₂ ω) P := (h₁.const_mul c₁).add (h₂.const_mul c₂)
  rw [integral_add hA h₄, integral_sub hB (h₃.const_mul c₃),
    integral_add (h₁.const_mul c₁) (h₂.const_mul c₂), integral_const_mul, integral_const_mul,
    integral_const_mul]

/-- The integrand of the fourth-moment identity, `L(x ↦ (x − y)⁴)(x)`. -/
def q4 (κ a b y x : ℝ) : ℝ := 3 * κ * (x * (1 - x)) * (x - y) ^ 2 + 2 * (a * (1 - x) - b * x) * (x - y) ^ 3

theorem q4_le (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : q4 κ a b y x ≤ (3 * κ / 4 + 2 * (a + b)) * (x - y) ^ 2 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have h1 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have h2 : |a * (1 - x) - b * x| ≤ a + b := by
    rw [abs_le]; constructor <;> nlinarith
  have h3 : |x - y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hs : 0 ≤ (x - y) ^ 2 := sq_nonneg _
  have h4 : (a * (1 - x) - b * x) * (x - y) ^ 3 ≤ (a + b) * (x - y) ^ 2 := by
    calc (a * (1 - x) - b * x) * (x - y) ^ 3 = ((a * (1 - x) - b * x) * (x - y)) * (x - y) ^ 2 := by
          ring
      _ ≤ |(a * (1 - x) - b * x) * (x - y)| * (x - y) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hs
      _ = |a * (1 - x) - b * x| * |x - y| * (x - y) ^ 2 := by rw [abs_mul]
      _ ≤ (a + b) * 1 * (x - y) ^ 2 := by gcongr
      _ = (a + b) * (x - y) ^ 2 := by ring
  have h5 : 3 * κ * (x * (1 - x)) * (x - y) ^ 2 ≤ 3 * κ / 4 * (x - y) ^ 2 := by
    have : 3 * κ * (x * (1 - x)) ≤ 3 * κ / 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hs
  unfold q4
  nlinarith

/-- **The fourth-moment bound** `E (U_v − U_w)⁴ ≤ quartC κ a b · (v − w)²`. -/
theorem jmp_integral_pow_four_sub_le (hU : IsJacobiMP κ a b P U) (hκ : 0 ≤ κ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) {w v : ℝ} (hwv : w ≤ v) :
    ∫ ω, (U v ω - U w ω) ^ 4 ∂P ≤ quartC κ a b * (v - w) ^ 2 := by
  have hI : ∀ (j n : ℕ), Integrable (fun ω => U w ω ^ j * (U v ω ^ n - U w ω ^ n)) P := fun j n =>
    ((jmp_integrable_pow_mul_pow hU j n w v).sub (jmp_integrable_pow_mul_pow hU j n w w)).congr
      (ae_of_all _ fun ω => by simp only [Pi.sub_apply]; ring)
  have hG : ∀ (j n : ℕ), Integrable (fun ω => U w ω ^ j * genInt κ a b U n w v ω) P := fun j n =>
    jmp_integrable_pow_mul_genInt hU j n hwv
  have hsplit : ∫ ω, (U v ω - U w ω) ^ 4 ∂P =
      -4 * ∫ ω, U w ω ^ 3 * (U v ω ^ 1 - U w ω ^ 1) ∂P + 6 * ∫ ω, U w ω ^ 2 * (U v ω ^ 2 - U w ω ^ 2) ∂P
      - 4 * ∫ ω, U w ω ^ 1 * (U v ω ^ 3 - U w ω ^ 3) ∂P + ∫ ω, U w ω ^ 0 * (U v ω ^ 4 - U w ω ^ 4) ∂P := by
    rw [← integral_comb4 (hI 3 1) (hI 2 2) (hI 1 3) (hI 0 4)]
    congr 1; funext ω; ring
  rw [hsplit, jmp_integral_mul_pow_sub hU 3 1 hwv, jmp_integral_mul_pow_sub hU 2 2 hwv,
    jmp_integral_mul_pow_sub hU 1 3 hwv, jmp_integral_mul_pow_sub hU 0 4 hwv,
    ← integral_comb4 (hG 3 1) (hG 2 2) (hG 1 3) (hG 0 4)]
  -- the pointwise identity with `q4`
  have hrw : ∀ ω, -4 * (U w ω ^ 3 * genInt κ a b U 1 w v ω) + 6 * (U w ω ^ 2 * genInt κ a b U 2 w v ω) -
      4 * (U w ω ^ 1 * genInt κ a b U 3 w v ω) + U w ω ^ 0 * genInt κ a b U 4 w v ω =
      ∫ y in w..v, q4 κ a b (U w ω) (U y ω) := fun ω => by
    have e : (fun y => q4 κ a b (U w ω) (U y ω)) = fun y =>
        -4 * (U w ω ^ 3 * (dcoef κ a 1 * U y ω ^ (1 - 1) + ccoef κ a b 1 * U y ω ^ 1)) +
          6 * (U w ω ^ 2 * (dcoef κ a 2 * U y ω ^ (2 - 1) + ccoef κ a b 2 * U y ω ^ 2)) -
          4 * (U w ω ^ 1 * (dcoef κ a 3 * U y ω ^ (3 - 1) + ccoef κ a b 3 * U y ω ^ 3)) +
          U w ω ^ 0 * (dcoef κ a 4 * U y ω ^ (4 - 1) + ccoef κ a b 4 * U y ω ^ 4) := by
      funext y; simp only [q4, dcoef, ccoef]; norm_num; ring
    have i1 := ((jmp_intervalIntegrable_gen hU 1 w v ω).const_mul (U w ω ^ 3)).const_mul (-4)
    have i2 := ((jmp_intervalIntegrable_gen hU 2 w v ω).const_mul (U w ω ^ 2)).const_mul 6
    have i3 := ((jmp_intervalIntegrable_gen hU 3 w v ω).const_mul (U w ω ^ 1)).const_mul 4
    have i4 := (jmp_intervalIntegrable_gen hU 4 w v ω).const_mul (U w ω ^ 0)
    rw [e, intervalIntegral.integral_add ((i1.add i2).sub i3) i4, intervalIntegral.integral_sub (i1.add i2) i3,
      intervalIntegral.integral_add i1 i2]
    simp only [intervalIntegral.integral_const_mul, genInt]
  simp only [hrw]
  -- Fubini and the second-moment bound
  have hm2 : Measurable fun p : ℝ × Ω => U p.1 p.2 :=
    hU.measurable_uncurry.comp measurable_swap
  have hq4m : Measurable fun p : ℝ × Ω => q4 κ a b (U w p.2) (U p.1 p.2) := by
    have hw' : Measurable fun p : ℝ × Ω => U w p.2 := (hU.measurable w).comp measurable_snd
    unfold q4; fun_prop
  set C₁ := 3 * κ / 4 + 2 * (a + b) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hpt : ∀ ω, ∫ y in w..v, q4 κ a b (U w ω) (U y ω) ≤ ∫ y in w..v, C₁ * (U y ω - U w ω) ^ 2 := fun ω => by
    have hc := hU.continuous ω
    refine intervalIntegral.integral_mono_on hwv ?_ ?_ fun y _ => ?_
    · exact (show Continuous fun y => q4 κ a b (U w ω) (U y ω) by unfold q4; fun_prop).intervalIntegrable _ _
    · exact (show Continuous fun y => C₁ * (U y ω - U w ω) ^ 2 by fun_prop).intervalIntegrable _ _
    · exact q4_le hκ ha hb (hU.mem_Icc y ω) (hU.mem_Icc w ω)
  have hbd : ∀ p : ℝ × Ω, ‖C₁ * (U p.1 p.2 - U w p.2) ^ 2‖ ≤ C₁ * 1 := fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := hU.mem_Icc p.1 p.2
    have h2 := hU.mem_Icc w p.2
    gcongr
    rw [sq_le_one_iff_abs_le_one, abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have : IsFiniteMeasure (volume.restrict (uIoc w v)) := by rw [uIoc_of_le hwv]; infer_instance
  have hsq_int : Integrable (fun p : ℝ × Ω => C₁ * (U p.1 p.2 - U w p.2) ^ 2)
      ((volume.restrict (uIoc w v)).prod P) :=
    Integrable.of_bound (by
      have hw' : Measurable fun p : ℝ × Ω => U w p.2 := (hU.measurable w).comp measurable_snd
      fun_prop) _ (ae_of_all _ hbd)
  have hswap := intervalIntegral_integral_swap (μ := P)
    (f := fun y ω => C₁ * (U y ω - U w ω) ^ 2) hsq_int
  have hq4_int : Integrable (fun ω => ∫ y in w..v, q4 κ a b (U w ω) (U y ω)) P := by
    refine Integrable.of_bound ?_ ((3 * κ / 4 + 2 * (a + b)) * 1 * |v - w|) (ae_of_all _ fun ω => ?_)
    · have : (fun ω => ∫ y in w..v, q4 κ a b (U w ω) (U y ω)) = fun ω =>
          ∫ y in Ioc w v, q4 κ a b (U w ω) (U y ω) := by
        funext ω; simp only [intervalIntegral.integral_of_le hwv]
      rw [this]
      exact ((hq4m.comp measurable_swap).stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Ioc w v))).aestronglyMeasurable
    · refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := (3 * κ / 4 + 2 * (a + b)) * 1) fun y _ => ?_).trans (le_of_eq ?_)
      · have h1 := hU.mem_Icc y ω
        have h2 := hU.mem_Icc w ω
        rw [Real.norm_eq_abs]
        unfold q4
        have hx1 : |U y ω * (1 - U y ω)| ≤ 1 / 4 := by
          rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, sq_nonneg (U y ω - 1 / 2)]
        have hx2 : |a * (1 - U y ω) - b * U y ω| ≤ a + b := by
          rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2]
        have hx3 : |U y ω - U w ω| ≤ 1 := by rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        calc |3 * κ * (U y ω * (1 - U y ω)) * (U y ω - U w ω) ^ 2 +
              2 * (a * (1 - U y ω) - b * U y ω) * (U y ω - U w ω) ^ 3|
            ≤ 3 * κ * (1 / 4) * 1 + 2 * (a + b) * 1 := by
              refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3),
                  abs_of_nonneg hκ]
                gcongr
                exact pow_le_one₀ (abs_nonneg _) hx3
              · rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
                gcongr
                exact pow_le_one₀ (abs_nonneg _) hx3
          _ = (3 * κ / 4 + 2 * (a + b)) * 1 := by ring
      · rfl
  calc ∫ ω, (∫ y in w..v, q4 κ a b (U w ω) (U y ω)) ∂P
      ≤ ∫ ω, (∫ y in w..v, C₁ * (U y ω - U w ω) ^ 2) ∂P :=
        integral_mono hq4_int (hsq_int.integral_prod_right.congr (ae_of_all _ fun ω => by
          simp only [intervalIntegral.integral_of_le hwv, uIoc_of_le hwv])) hpt
    _ = ∫ y in w..v, ∫ ω, C₁ * (U y ω - U w ω) ^ 2 ∂P := hswap.symm
    _ ≤ ∫ y in w..v, C₁ * ((κ / 8 + (a + b)) * (y - w)) := by
        refine intervalIntegral.integral_mono_on hwv ?_
          (Continuous.intervalIntegrable (by fun_prop) _ _) fun y hy => ?_
        · exact intervalIntegrable_iff.2 hsq_int.integral_prod_left
        · rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (jmp_integral_sq_sub_le hU hκ ha hb hy.1) hC₁0
    _ = quartC κ a b * (v - w) ^ 2 := by
        simp only [quartC, hC₁]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_sub_right (fun y => y) w, integral_id]
        ring

end Quartic

/-! ### Convergence of the mixed moments as the parameters converge -/

section Converge

/-- **Variation of constants** for a linear equation in integral form: if `M`, `f` are continuous and
`M x − M w = ∫_w^x (c M + f)` for `x ≥ w`, then `M x = e^{c(x−w)} M w + ∫_w^x e^{c(x−y)} f(y) dy`. -/
theorem eq_variation_of_constants {M f : ℝ → ℝ} (hM : Continuous M) (hf : Continuous f) {c w : ℝ}
    (hint : ∀ x, w ≤ x → M x - M w = ∫ y in w..x, (c * M y + f y)) {x : ℝ} (hx : w ≤ x) :
    M x = exp (c * (x - w)) * M w + ∫ y in w..x, exp (c * (x - y)) * f y := by
  have hg : Continuous fun y => c * M y + f y := (hM.const_mul c).add hf
  set F : ℝ → ℝ := fun y => M w + ∫ t in w..y, (c * M t + f t) with hFdef
  have hF : ∀ y, HasDerivAt F (c * M y + f y) y := fun y =>
    (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt).const_add _
  have hFM : ∀ y, w ≤ y → F y = M y := fun y hy => by
    simp only [hFdef]; linarith [hint y hy]
  have he : Continuous fun z => exp (-(c * (z - w))) * f z :=
    ((continuous_id.sub continuous_const).const_mul c).neg.rexp.mul hf
  set G : ℝ → ℝ := fun y => ∫ z in w..y, exp (-(c * (z - w))) * f z with hGdef
  have hG : ∀ y, HasDerivAt G (exp (-(c * (y - w))) * f y) y := fun y =>
    intervalIntegral.integral_hasDerivAt_right (he.intervalIntegrable _ _)
      (he.stronglyMeasurableAtFilter _ _) he.continuousAt
  set N : ℝ → ℝ := fun y => F y * exp (-(c * (y - w))) - G y with hNdef
  have hN : ∀ y, HasDerivAt N ((c * M y + f y) * exp (-(c * (y - w))) +
      F y * (exp (-(c * (y - w))) * -(c * 1)) - exp (-(c * (y - w))) * f y) y := fun y => by
    have h1 : HasDerivAt (fun y => -(c * (y - w))) (-(c * 1)) y :=
      (((hasDerivAt_id y).sub_const w).const_mul c).neg
    exact ((hF y).mul h1.exp).sub (hG y)
  have hcont : ContinuousOn N (Icc w x) :=
    (continuous_iff_continuousAt.2 fun y => (hN y).continuousAt).continuousOn
  have hconst := constant_of_has_deriv_right_zero hcont (fun y hy => by
    have := (hN y).hasDerivWithinAt (s := Ici y)
    convert this using 1
    rw [← hFM y hy.1]
    ring) x ⟨hx, le_rfl⟩
  simp only [hNdef, hGdef, sub_self, mul_zero, neg_zero, exp_zero, mul_one,
    intervalIntegral.integral_same, sub_zero] at hconst
  rw [hFM x hx, hFM w le_rfl] at hconst
  have hmul : ∫ y in w..x, exp (c * (x - y)) * f y =
      exp (c * (x - w)) * ∫ z in w..x, exp (-(c * (z - w))) * f z := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [← mul_assoc, ← exp_add]
    congr 2; ring
  rw [hmul]
  have he1 : exp (c * (x - w)) * exp (-(c * (x - w))) = 1 := by rw [← exp_add]; simp
  calc M x = exp (c * (x - w)) * (M x * exp (-(c * (x - w)))) := by
        rw [← mul_assoc, mul_comm (exp _) (M x), mul_assoc, he1, mul_one]
    _ = exp (c * (x - w)) * (M w + ∫ z in w..x, exp (-(c * (z - w))) * f z) := by
        rw [← hconst]; ring
    _ = _ := by ring

theorem continuous_ccoef (κ : ℝ) (n : ℕ) : Continuous fun p : ℝ × ℝ => ccoef κ p.1 p.2 n := by
  unfold ccoef; fun_prop

theorem continuous_dcoef (κ : ℝ) (n : ℕ) : Continuous fun a : ℝ => dcoef κ a n := by
  unfold dcoef; fun_prop

/-- The beta moments are continuous in the parameters where `a + b > 0`. -/
theorem tendsto_jacobiMoment {κ a b : ℝ} (hκ : 0 ≤ κ) (hab : 0 < a + b) {am bm : ℕ → ℝ}
    (ham : Tendsto am atTop (𝓝 a)) (hbm : Tendsto bm atTop (𝓝 b)) (n : ℕ) :
    Tendsto (fun m => jacobiMoment κ (am m) (bm m) n) atTop (𝓝 (jacobiMoment κ a b n)) := by
  induction n with
  | zero => simp only [jacobiMoment]; exact tendsto_const_nhds
  | succ n ih =>
    simp only [jacobiMoment]
    have hc := ccoef_neg hκ hab (Nat.le_add_left 1 n)
    have h1 : Tendsto (fun m => dcoef κ (am m) (n + 1)) atTop (𝓝 (dcoef κ a (n + 1))) :=
      ((continuous_dcoef κ (n + 1)).tendsto a).comp ham
    have h2 : Tendsto (fun m => ccoef κ (am m) (bm m) (n + 1)) atTop (𝓝 (ccoef κ a b (n + 1))) :=
      ((continuous_ccoef κ (n + 1)).tendsto (a, b)).comp (ham.prodMk_nhds hbm)
    exact ih.mul (h1.div h2.neg (by linarith))

/-- The moment system of `IsJacobiMP.momF_sub` in variation-of-constants form. -/
theorem momF_eq_vc {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {V : ℝ → Ω' → ℝ} {κ a' b' : ℝ} (hV : IsJacobiMP κ a' b' P' V) {k : ℕ} (s' : Fin k → ℝ)
    (e' : Fin k → ℕ) (n : ℕ) {w x : ℝ} (hs'w : ∀ i, s' i ≤ w) (hx : w ≤ x) :
    momF P' V s' e' (n + 1) x = exp (ccoef κ a' b' (n + 1) * (x - w)) * momF P' V s' e' (n + 1) w +
      ∫ y in w..x, exp (ccoef κ a' b' (n + 1) * (x - y)) * (dcoef κ a' (n + 1) * momF P' V s' e' n y) := by
  refine eq_variation_of_constants (hV.continuous_momF s' e' (n + 1))
    ((hV.continuous_momF s' e' n).const_mul _) (fun x' hx' => ?_) hx
  rw [hV.momF_sub s' e' (n + 1) hs'w hx']
  simp only [Nat.add_sub_cancel]

variable {κ a b : ℝ} {am bm : ℕ → ℝ} {Ωs : ℕ → Type*} [∀ m, MeasurableSpace (Ωs m)]
  {Ps : ∀ m, Measure (Ωs m)} [∀ m, IsProbabilityMeasure (Ps m)] {Us : ∀ m, ℝ → Ωs m → ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {U : ℝ → Ω → ℝ}

/-- **Convergence of the mixed moments.** Solutions of the Jacobi martingale problem with parameters
`(κ, a_m, b_m) → (κ, a, b)`: every mixed moment `E ∏ U_{s_i}^{k_i}` converges. -/
theorem tendsto_integral_prodPow (hκ : 0 ≤ κ) (hab : 0 < a + b) (habm : ∀ m, 0 < am m + bm m)
    (ham : Tendsto am atTop (𝓝 a)) (hbm : Tendsto bm atTop (𝓝 b))
    (hUs : ∀ m, IsJacobiMP κ (am m) (bm m) (Ps m) (Us m)) (hU : IsJacobiMP κ a b P U) :
    ∀ (k : ℕ) (s : Fin k → ℝ) (e : Fin k → ℕ),
      Tendsto (fun m => ∫ ω, prodPow (Us m) s e ω ∂(Ps m)) atTop (𝓝 (∫ ω, prodPow U s e ω ∂P)) := by
  intro k
  induction k with
  | zero =>
    intro s e
    have h1 : ∀ m, ∫ ω, prodPow (Us m) s e ω ∂(Ps m) = 1 := fun m => by simp [prodPow]
    have h1' : ∫ ω, prodPow U s e ω ∂P = 1 := by simp [prodPow]
    simp only [h1, h1']
    exact tendsto_const_nhds
  | succ k ih =>
    intro s e
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ s Finset.univ_nonempty
    have hsplit : ∀ m ω, prodPow (Us m) s e ω =
        prodPow (Us m) (s ∘ j.succAbove) (e ∘ j.succAbove) ω * Us m (s j) ω ^ e j := fun m ω => by
      simp only [prodPow, Fin.prod_univ_succAbove _ j, Function.comp_apply]; ring
    have hsplit' : ∀ ω, prodPow U s e ω =
        prodPow U (s ∘ j.succAbove) (e ∘ j.succAbove) ω * U (s j) ω ^ e j := fun ω => by
      simp only [prodPow, Fin.prod_univ_succAbove _ j, Function.comp_apply]; ring
    simp only [hsplit, hsplit']
    set s' := s ∘ j.succAbove with hs'
    set e' := e ∘ j.succAbove
    have hs'v : ∀ i, s' i ≤ s j := fun i => hj _ (Finset.mem_univ _)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have e0 : ∀ m ω, prodPow (Us m) s' e' ω = 1 := fun m ω => by simp [prodPow]
      have e0' : ∀ ω, prodPow U s' e' ω = 1 := fun ω => by simp [prodPow]
      simp only [e0, e0', one_mul]
      have h1 : ∀ m, ∫ ω, Us m (s j) ω ^ e j ∂(Ps m) = jacobiMoment κ (am m) (bm m) (e j) :=
        fun m => (hUs m).moment_eq hκ (habm m) _ _
      simp only [h1, hU.moment_eq hκ hab]
      exact tendsto_jacobiMoment hκ hab ham hbm _
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ s'
      (Finset.univ_nonempty_iff.2 ⟨⟨0, hk⟩⟩)
    have hs'w : ∀ i, s' i ≤ s' i₀ := fun i => hi₀ _ (Finset.mem_univ _)
    have key : ∀ n x, s' i₀ ≤ x →
        Tendsto (fun m => momF (Ps m) (Us m) s' e' n x) atTop (𝓝 (momF P U s' e' n x)) := by
      intro n
      induction n with
      | zero =>
        intro x _
        simp only [momF, pow_zero, mul_one]
        exact ih s' e'
      | succ n ihn =>
        intro x hx
        set w := s' i₀
        -- the values at `w`
        have hw : Tendsto (fun m => momF (Ps m) (Us m) s' e' (n + 1) w) atTop
            (𝓝 (momF P U s' e' (n + 1) w)) := by
          have h1 := ih s' (fun i => e' i + if i = i₀ then n + 1 else 0)
          simp only [prodPow_add_single] at h1
          exact h1
        -- the variation-of-constants formulas
        simp only [momF_eq_vc (hUs _) s' e' n hs'w hx, momF_eq_vc hU s' e' n hs'w hx]
        have hc : Tendsto (fun m => ccoef κ (am m) (bm m) (n + 1)) atTop (𝓝 (ccoef κ a b (n + 1))) :=
          ((continuous_ccoef κ (n + 1)).tendsto (a, b)).comp (ham.prodMk_nhds hbm)
        have hd : Tendsto (fun m => dcoef κ (am m) (n + 1)) atTop (𝓝 (dcoef κ a (n + 1))) :=
          ((continuous_dcoef κ (n + 1)).tendsto a).comp ham
        refine ((((hc.mul_const (x - w)).rexp).mul hw)).add ?_
        -- dominated convergence for the integral term
        have hcb : ∀ᶠ m in atTop, |ccoef κ (am m) (bm m) (n + 1)| ≤ |ccoef κ a b (n + 1)| + 1 :=
          (hc.abs.eventually (gt_mem_nhds (lt_add_one _))).mono fun m h => h.le
        have hdb : ∀ᶠ m in atTop, |dcoef κ (am m) (n + 1)| ≤ |dcoef κ a (n + 1)| + 1 :=
          (hd.abs.eventually (gt_mem_nhds (lt_add_one _))).mono fun m h => h.le
        refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
          (fun _ => exp ((|ccoef κ a b (n + 1)| + 1) * (x - w)) * (|dcoef κ a (n + 1)| + 1)) ?_ ?_
          intervalIntegrable_const ?_
        · exact Eventually.of_forall fun m => (((continuous_const.mul
            (continuous_const.sub continuous_id)).rexp).mul
            ((((hUs m).continuous_momF s' e' n)).const_mul _)).aestronglyMeasurable
        · filter_upwards [hcb, hdb] with m hcm hdm
          refine ae_of_all _ fun y hy => ?_
          rw [uIoc_of_le hx] at hy
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos _)]
          have hm1 := (hUs m).abs_momF_le s' e' n y
          refine mul_le_mul ?_ ?_ (by positivity) (exp_pos _).le
          · refine exp_le_exp.2 ?_
            calc ccoef κ (am m) (bm m) (n + 1) * (x - y) ≤ |ccoef κ (am m) (bm m) (n + 1)| * (x - y) :=
                  mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith [hy.2])
              _ ≤ (|ccoef κ a b (n + 1)| + 1) * (x - w) := by
                  gcongr
                  · linarith [hy.2]
                  · linarith [hy.1]
          · calc |dcoef κ (am m) (n + 1)| * |momF (Ps m) (Us m) s' e' n y|
                ≤ (|dcoef κ a (n + 1)| + 1) * 1 := mul_le_mul hdm hm1 (abs_nonneg _) (by positivity)
              _ = _ := mul_one _
        · refine ae_of_all _ fun y hy => ?_
          rw [uIoc_of_le hx] at hy
          exact ((hc.mul_const (x - y)).rexp).mul (hd.mul (ihn y hy.1.le))
    exact key (e j) (s j) (hs'v i₀)

end Converge

end Aux4

end Supp12

end InteractingSLE
