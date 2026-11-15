/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.Bessel.Regularized
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import QuantumZipper.Proofs.ItoLite.Dynkin

/-!
# The test function of the Bessel occupation estimate

Packet PROVE-BESSEL. For `ε > 0` let `m = softMax ε` be the smooth upper envelope
`m x = (x + √(x² + ε²) + ε) / 2` of `max x ε` (it satisfies `ε/2 < m`, `x ≤ m x ≤ max x 0 + ε`,
`0 ≤ m' ≤ 1`, `0 ≤ m'' ≤ 1/(2ε)`). For `0 < p < 1` put `g = p m^{p-1}` (`testFunDeriv`) and
`F x = ∫₀ˣ g` (`testFun`). Then `F` is `C³` with bounded first, second and third derivatives, and for
the regularized Bessel drift `b = c / max · ε` and `1 - p ≤ c/8` the Dynkin generator satisfies

  `LF x = g x · b x + ½ g' x ≥ (p/4) (max x ε)^{p-1} b x ≥ 0`   (`le_dynkinGen_testFun`).

Since `g x ≤ p x^{p-1}` for `x > 0`, `F y ≤ (max y 0)^p` (`testFun_le`), and `F x ≥ 0` for `x ≥ 0`.

This is the regularized form of the computation `L x^p = (p/2)(p - 1 + 2c) x^{p-2} > 0` for the Bessel
generator `½ ∂² + (c/x) ∂`, `p > 1 - 2c` (Revuz–Yor XI.1; here `p` is close to `1`).
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace InteractingSLE

namespace Bessel

/-! ### The smooth envelope `softMax` -/

/-- The smooth upper envelope `(x + √(x² + ε²) + ε) / 2` of `max x ε`. -/
def softMax (ε x : ℝ) : ℝ := (x + √(x ^ 2 + ε ^ 2) + ε) / 2

/-- The derivative of `softMax ε`. -/
def softMaxDeriv (ε x : ℝ) : ℝ := (1 + x / √(x ^ 2 + ε ^ 2)) / 2

/-- The second derivative of `softMax ε`. -/
def softMaxDeriv2 (ε x : ℝ) : ℝ := ε ^ 2 / (2 * ((x ^ 2 + ε ^ 2) * √(x ^ 2 + ε ^ 2)))

variable {ε : ℝ}

theorem sq_add_sq_pos (hε : 0 < ε) (x : ℝ) : 0 < x ^ 2 + ε ^ 2 := by positivity

theorem sqrt_sq_add_sq_pos (hε : 0 < ε) (x : ℝ) : 0 < √(x ^ 2 + ε ^ 2) :=
  Real.sqrt_pos.2 (sq_add_sq_pos hε x)

theorem abs_lt_sqrt_sq_add_sq (hε : 0 < ε) (x : ℝ) : |x| < √(x ^ 2 + ε ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith [pow_pos hε 2])

theorem sqrt_sq_add_sq_le (hε : 0 < ε) (x : ℝ) : √(x ^ 2 + ε ^ 2) ≤ |x| + ε := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg x, sq_abs x, hε]

theorem ε_half_lt_softMax (hε : 0 < ε) (x : ℝ) : ε / 2 < softMax ε x := by
  have h := abs_lt_sqrt_sq_add_sq hε x
  have : -x ≤ |x| := neg_le_abs x
  unfold softMax; linarith

theorem softMax_pos (hε : 0 < ε) (x : ℝ) : 0 < softMax ε x :=
  (half_pos hε).trans (ε_half_lt_softMax hε x)

theorem le_softMax (hε : 0 < ε) (x : ℝ) : x ≤ softMax ε x := by
  have h := abs_lt_sqrt_sq_add_sq hε x
  have : x ≤ |x| := le_abs_self x
  unfold softMax; linarith

theorem softMax_le (hε : 0 < ε) (x : ℝ) : softMax ε x ≤ max x 0 + ε := by
  have h := sqrt_sq_add_sq_le hε x
  unfold softMax
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h; rw [max_eq_left hx]; linarith
  · rw [abs_of_nonpos hx] at h; rw [max_eq_right hx]; linarith

theorem softMaxDeriv_nonneg (hε : 0 < ε) (x : ℝ) : 0 ≤ softMaxDeriv ε x := by
  have h := abs_lt_sqrt_sq_add_sq hε x
  have hs := sqrt_sq_add_sq_pos hε x
  have : -1 ≤ x / √(x ^ 2 + ε ^ 2) := by
    rw [le_div_iff₀ hs]; linarith [neg_abs_le x]
  unfold softMaxDeriv; linarith

theorem softMaxDeriv_le_one (hε : 0 < ε) (x : ℝ) : softMaxDeriv ε x ≤ 1 := by
  have h := abs_lt_sqrt_sq_add_sq hε x
  have hs := sqrt_sq_add_sq_pos hε x
  have : x / √(x ^ 2 + ε ^ 2) ≤ 1 := by
    rw [div_le_iff₀ hs]; linarith [le_abs_self x]
  unfold softMaxDeriv; linarith

theorem softMaxDeriv2_nonneg (hε : 0 < ε) (x : ℝ) : 0 ≤ softMaxDeriv2 ε x := by
  have := sqrt_sq_add_sq_pos hε x
  have := sq_add_sq_pos hε x
  unfold softMaxDeriv2; positivity

theorem softMaxDeriv2_le (hε : 0 < ε) (x : ℝ) : softMaxDeriv2 ε x ≤ 1 / (2 * ε) := by
  have hs := sqrt_sq_add_sq_pos hε x
  have hq := sq_add_sq_pos hε x
  have hsε : ε ≤ √(x ^ 2 + ε ^ 2) := by
    rw [Real.le_sqrt hε.le hq.le]; nlinarith [sq_nonneg x]
  have hqε : ε ^ 2 ≤ x ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg x]
  have hprod : ε ^ 2 * ε ≤ (x ^ 2 + ε ^ 2) * √(x ^ 2 + ε ^ 2) :=
    mul_le_mul hqε hsε hε.le hq.le
  unfold softMaxDeriv2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hε 2]

theorem hasDerivAt_sqrt_sq_add_sq (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (fun y => √(y ^ 2 + ε ^ 2)) (x / √(x ^ 2 + ε ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + ε ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (ε ^ 2)
  have h2 := h1.sqrt (sq_add_sq_pos hε x).ne'
  refine h2.congr_deriv ?_
  have := sqrt_sq_add_sq_pos hε x
  field_simp

theorem hasDerivAt_softMax (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (softMax ε) (softMaxDeriv ε x) x := by
  have h := ((hasDerivAt_id x).add (hasDerivAt_sqrt_sq_add_sq hε x)).add_const ε
  have h2 := h.div_const 2
  unfold softMax softMaxDeriv
  exact h2.congr_deriv (by simp)

theorem hasDerivAt_softMaxDeriv (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (softMaxDeriv ε) (softMaxDeriv2 ε x) x := by
  have hs := sqrt_sq_add_sq_pos hε x
  have h := ((hasDerivAt_id x).div (hasDerivAt_sqrt_sq_add_sq hε x) hs.ne').const_add 1
  have h2 := h.div_const 2
  unfold softMaxDeriv softMaxDeriv2
  refine h2.congr_deriv ?_
  have hsq : √(x ^ 2 + ε ^ 2) ^ 2 = x ^ 2 + ε ^ 2 := Real.sq_sqrt (sq_add_sq_pos hε x).le
  simp only [id]
  field_simp
  rw [hsq]
  ring

theorem contDiff_softMax (hε : 0 < ε) {n : WithTop ℕ∞} : ContDiff ℝ n (softMax ε) := by
  have hq : ContDiff ℝ n (fun y : ℝ => y ^ 2 + ε ^ 2) := (contDiff_id.pow 2).add contDiff_const
  have hs : ContDiff ℝ n (fun y : ℝ => √(y ^ 2 + ε ^ 2)) :=
    hq.sqrt fun y => (sq_add_sq_pos hε y).ne'
  exact ((contDiff_id.add hs).add contDiff_const).div_const 2

/-! ### The derivative `g = p m^{p-1}` of the test function and its derivatives -/

/-- `g = p · (softMax ε)^{p-1}`, the derivative of the test function. -/
def testFunDeriv (p ε x : ℝ) : ℝ := p * softMax ε x ^ (p - 1)

/-- `g' = p (p - 1) m^{p-2} m'`. -/
def testFunDeriv2 (p ε x : ℝ) : ℝ :=
  p * (p - 1) * (softMax ε x ^ (p - 2) * softMaxDeriv ε x)

/-- `g'' = p (p - 1) ((p - 2) m^{p-3} m'² + m^{p-2} m'')`. -/
def testFunDeriv3 (p ε x : ℝ) : ℝ :=
  p * (p - 1) * ((p - 2) * softMax ε x ^ (p - 3) * softMaxDeriv ε x ^ 2
    + softMax ε x ^ (p - 2) * softMaxDeriv2 ε x)

variable {p : ℝ}

theorem hasDerivAt_testFunDeriv (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (testFunDeriv p ε) (testFunDeriv2 p ε x) x := by
  have h := ((hasDerivAt_softMax hε x).rpow_const (p := p - 1)
    (Or.inl (softMax_pos hε x).ne')).const_mul p
  unfold testFunDeriv testFunDeriv2
  refine h.congr_deriv ?_
  rw [show p - 1 - 1 = p - 2 by ring]
  ring

theorem hasDerivAt_testFunDeriv2 (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (testFunDeriv2 p ε) (testFunDeriv3 p ε x) x := by
  have h1 := (hasDerivAt_softMax hε x).rpow_const (p := p - 2) (Or.inl (softMax_pos hε x).ne')
  have h := (h1.mul (hasDerivAt_softMaxDeriv hε x)).const_mul (p * (p - 1))
  unfold testFunDeriv2 testFunDeriv3
  refine h.congr_deriv ?_
  rw [show p - 2 - 1 = p - 3 by ring]
  ring

theorem deriv_testFunDeriv (hε : 0 < ε) : deriv (testFunDeriv p ε) = testFunDeriv2 p ε :=
  funext fun x => (hasDerivAt_testFunDeriv hε x).deriv

theorem deriv_testFunDeriv2 (hε : 0 < ε) : deriv (testFunDeriv2 p ε) = testFunDeriv3 p ε :=
  funext fun x => (hasDerivAt_testFunDeriv2 hε x).deriv

theorem contDiff_testFunDeriv (hε : 0 < ε) {n : WithTop ℕ∞} :
    ContDiff ℝ n (testFunDeriv p ε) :=
  contDiff_const.mul ((contDiff_softMax hε).rpow_const_of_ne fun x => (softMax_pos hε x).ne')

theorem continuous_testFunDeriv (hε : 0 < ε) : Continuous (testFunDeriv p ε) :=
  (contDiff_testFunDeriv (n := 0) hε).continuous

theorem testFunDeriv_pos (hp : 0 < p) (hε : 0 < ε) (x : ℝ) : 0 < testFunDeriv p ε x :=
  mul_pos hp (Real.rpow_pos_of_pos (softMax_pos hε x) _)

/-- `m^r ≤ (ε/2)^r` for `r ≤ 0`. -/
theorem softMax_rpow_le (hε : 0 < ε) {r : ℝ} (hr : r ≤ 0) (x : ℝ) :
    softMax ε x ^ r ≤ (ε / 2) ^ r :=
  Real.rpow_le_rpow_of_nonpos (half_pos hε) (ε_half_lt_softMax hε x).le hr

theorem abs_testFunDeriv_le (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) (x : ℝ) :
    |testFunDeriv p ε x| ≤ p * (ε / 2) ^ (p - 1) := by
  rw [abs_of_pos (testFunDeriv_pos hp0 hε x)]
  exact mul_le_mul_of_nonneg_left (softMax_rpow_le hε (by linarith) x) hp0.le

theorem abs_testFunDeriv2_le (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) (x : ℝ) :
    |testFunDeriv2 p ε x| ≤ p * (1 - p) * (ε / 2) ^ (p - 2) := by
  have hm := softMax_rpow_le hε (r := p - 2) (by linarith) x
  have hm0 : 0 ≤ softMax ε x ^ (p - 2) := (Real.rpow_pos_of_pos (softMax_pos hε x) _).le
  have hd0 := softMaxDeriv_nonneg hε x
  have hd1 := softMaxDeriv_le_one hε x
  unfold testFunDeriv2
  rw [abs_mul, abs_mul, abs_of_pos hp0, abs_of_nonpos (by linarith : p - 1 ≤ 0),
    abs_of_nonneg (mul_nonneg hm0 hd0)]
  have : softMax ε x ^ (p - 2) * softMaxDeriv ε x ≤ (ε / 2) ^ (p - 2) := by
    calc softMax ε x ^ (p - 2) * softMaxDeriv ε x ≤ softMax ε x ^ (p - 2) * 1 :=
          mul_le_mul_of_nonneg_left hd1 hm0
      _ ≤ (ε / 2) ^ (p - 2) := by rw [mul_one]; exact hm
  have h1p : 0 ≤ -(p - 1) := by linarith
  calc p * -(p - 1) * (softMax ε x ^ (p - 2) * softMaxDeriv ε x)
      ≤ p * -(p - 1) * (ε / 2) ^ (p - 2) :=
        mul_le_mul_of_nonneg_left this (mul_nonneg hp0.le h1p)
    _ = p * (1 - p) * (ε / 2) ^ (p - 2) := by ring

theorem abs_testFunDeriv3_le (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) (x : ℝ) :
    |testFunDeriv3 p ε x| ≤
      p * (1 - p) * ((2 - p) * (ε / 2) ^ (p - 3) + (ε / 2) ^ (p - 2) * (1 / (2 * ε))) := by
  have hm3 := softMax_rpow_le hε (r := p - 3) (by linarith) x
  have hm2 := softMax_rpow_le hε (r := p - 2) (by linarith) x
  have hm30 : 0 ≤ softMax ε x ^ (p - 3) := (Real.rpow_pos_of_pos (softMax_pos hε x) _).le
  have hm20 : 0 ≤ softMax ε x ^ (p - 2) := (Real.rpow_pos_of_pos (softMax_pos hε x) _).le
  have hd0 := softMaxDeriv_nonneg hε x
  have hd1 := softMaxDeriv_le_one hε x
  have he0 := softMaxDeriv2_nonneg hε x
  have he1 := softMaxDeriv2_le hε x
  have hsq : softMaxDeriv ε x ^ 2 ≤ 1 := by nlinarith
  have hsq0 : 0 ≤ softMaxDeriv ε x ^ 2 := sq_nonneg _
  unfold testFunDeriv3
  rw [abs_mul, abs_mul, abs_of_pos hp0, abs_of_nonpos (by linarith : p - 1 ≤ 0),
    show -(p - 1) = 1 - p by ring]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hp0.le (by linarith))
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : p - 2 ≤ 0), abs_of_nonneg hm30,
      abs_of_nonneg hsq0, show -(p - 2) = 2 - p by ring]
    calc (2 - p) * softMax ε x ^ (p - 3) * softMaxDeriv ε x ^ 2
        ≤ (2 - p) * (ε / 2) ^ (p - 3) * 1 := by
          apply mul_le_mul _ hsq hsq0 (mul_nonneg (by linarith) (by positivity))
          exact mul_le_mul_of_nonneg_left hm3 (by linarith)
      _ = (2 - p) * (ε / 2) ^ (p - 3) := mul_one _
  · rw [abs_mul, abs_of_nonneg hm20, abs_of_nonneg he0]
    exact mul_le_mul hm2 he1 he0 (by positivity)

/-! ### The test function `F = ∫₀ˣ g` -/

/-- The test function `F x = ∫₀ˣ p · (softMax ε)^{p-1}`. -/
def testFun (p ε x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, testFunDeriv p ε s

theorem hasDerivAt_testFun (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (testFun p ε) (testFunDeriv p ε x) x :=
  ((continuous_testFunDeriv hε).integral_hasStrictDerivAt 0 x).hasDerivAt

theorem deriv_testFun (hε : 0 < ε) : deriv (testFun p ε) = testFunDeriv p ε :=
  funext fun x => (hasDerivAt_testFun hε x).deriv

theorem contDiff_testFun (hε : 0 < ε) : ContDiff ℝ 3 (testFun p ε) := by
  rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_testFun hε x).differentiableAt, fun h => ?_, ?_⟩
  · exact absurd h (by decide)
  · rw [deriv_testFun hε]; exact contDiff_testFunDeriv hε

theorem iteratedDeriv_two_testFun (hε : 0 < ε) :
    iteratedDeriv 2 (testFun p ε) = testFunDeriv2 p ε := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_testFun hε, deriv_testFunDeriv hε]

theorem iteratedDeriv_three_testFun (hε : 0 < ε) :
    iteratedDeriv 3 (testFun p ε) = testFunDeriv3 p ε := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_testFun hε, deriv_testFunDeriv2 hε]

/-- A bound for the first three derivatives of the test function. -/
def testFunBound (p ε : ℝ) : ℝ :=
  p * (ε / 2) ^ (p - 1) + p * (1 - p) * (ε / 2) ^ (p - 2)
    + p * (1 - p) * ((2 - p) * (ε / 2) ^ (p - 3) + (ε / 2) ^ (p - 2) * (1 / (2 * ε)))

theorem norm_derivs_testFun_le (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) (x : ℝ) :
    ‖fderiv ℝ (testFun p ε) x‖ ≤ testFunBound p ε ∧
      ‖iteratedFDeriv ℝ 2 (testFun p ε) x‖ ≤ testFunBound p ε ∧
      ‖iteratedFDeriv ℝ 3 (testFun p ε) x‖ ≤ testFunBound p ε := by
  have h1 := abs_testFunDeriv_le hp0 hp1 hε x
  have h2 := abs_testFunDeriv2_le hp0 hp1 hε x
  have h3 := abs_testFunDeriv3_le hp0 hp1 hε x
  have a1 : 0 ≤ p * (ε / 2) ^ (p - 1) := by positivity
  have a2 : 0 ≤ p * (1 - p) * (ε / 2) ^ (p - 2) :=
    mul_nonneg (mul_nonneg hp0.le (by linarith)) (by positivity)
  have a3 : 0 ≤ p * (1 - p) * ((2 - p) * (ε / 2) ^ (p - 3) + (ε / 2) ^ (p - 2) * (1 / (2 * ε))) :=
    mul_nonneg (mul_nonneg hp0.le (by linarith))
      (add_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity))
  unfold testFunBound
  refine ⟨?_, ?_, ?_⟩
  · rw [← norm_deriv_eq_norm_fderiv, deriv_testFun hε, Real.norm_eq_abs]; linarith
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_two_testFun hε,
      Real.norm_eq_abs]; linarith
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_three_testFun hε,
      Real.norm_eq_abs]; linarith

/-- The Dynkin generator of the regularized Bessel equation applied to the test function. -/
theorem dynkinGen_testFun_eq {c : ℝ} (hε : 0 < ε) (x : ℝ) :
    QuantumZipper.dynkinGen (regDrift c ε) (1 : ℝ) (testFun p ε) x
      = testFunDeriv p ε x * regDrift c ε x + 1 / 2 * testFunDeriv2 p ε x := by
  unfold QuantumZipper.dynkinGen
  rw [fderiv_eq_smul_deriv, deriv_testFun hε, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    iteratedDeriv_two_testFun hε]
  simp [smul_eq_mul, mul_comm]

/-! ### The generator inequality -/

theorem softMax_le_two_mul_max (hε : 0 < ε) (x : ℝ) : softMax ε x ≤ 2 * max x ε := by
  have h := softMax_le hε x
  have h1 : max x 0 ≤ max x ε := max_le_max le_rfl hε.le
  have h2 : ε ≤ max x ε := le_max_right _ _
  linarith

theorem half_max_le_softMax (hε : 0 < ε) (x : ℝ) : max x ε / 2 ≤ softMax ε x := by
  rcases le_total x ε with hx | hx
  · rw [max_eq_right hx]; exact (ε_half_lt_softMax hε x).le
  · rw [max_eq_left hx]
    have := le_softMax hε x
    linarith

/-- `g ≥ (p/2) (max x ε)^{p-1}`. -/
theorem testFunDeriv_ge (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) (x : ℝ) :
    p / 2 * max x ε ^ (p - 1) ≤ testFunDeriv p ε x := by
  set M := max x ε
  have hM : 0 < M := hε.trans_le (le_max_right _ _)
  have hm := softMax_le_two_mul_max hε x
  have h1 : (2 * M) ^ (p - 1) ≤ softMax ε x ^ (p - 1) :=
    Real.rpow_le_rpow_of_nonpos (softMax_pos hε x) hm (by linarith)
  have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ (p - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_neg_one] at h2
  rw [Real.mul_rpow (by norm_num) hM.le] at h1
  have hMp : 0 ≤ M ^ (p - 1) := (Real.rpow_pos_of_pos hM _).le
  unfold testFunDeriv
  calc p / 2 * M ^ (p - 1) = p * (2⁻¹ * M ^ (p - 1)) := by ring
    _ ≤ p * (2 ^ (p - 1) * M ^ (p - 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hMp) hp0.le
    _ ≤ p * softMax ε x ^ (p - 1) := mul_le_mul_of_nonneg_left h1 hp0.le

/-- `g' ≥ -4 p (1 - p) (max x ε)^{p-2}`. -/
theorem testFunDeriv2_ge (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) (x : ℝ) :
    -(4 * p * (1 - p) * max x ε ^ (p - 2)) ≤ testFunDeriv2 p ε x := by
  set M := max x ε
  have hM : 0 < M := hε.trans_le (le_max_right _ _)
  have hm := half_max_le_softMax hε x
  have h1 : softMax ε x ^ (p - 2) ≤ (M / 2) ^ (p - 2) :=
    Real.rpow_le_rpow_of_nonpos (half_pos hM) hm (by linarith)
  have h2 : (2 : ℝ) ^ (-2 : ℝ) ≤ 2 ^ (p - 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h22 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num), show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h22] at h2
  have h3 : (M / 2) ^ (p - 2) ≤ 4 * M ^ (p - 2) := by
    rw [Real.div_rpow hM.le (by norm_num)]
    have hpos : 0 < (2 : ℝ) ^ (p - 2) := by positivity
    rw [div_le_iff₀ hpos]
    have hMp : 0 ≤ M ^ (p - 2) := (Real.rpow_pos_of_pos hM _).le
    nlinarith
  have hm0 : 0 ≤ softMax ε x ^ (p - 2) := (Real.rpow_pos_of_pos (softMax_pos hε x) _).le
  have hd0 := softMaxDeriv_nonneg hε x
  have hd1 := softMaxDeriv_le_one hε x
  have hprod : softMax ε x ^ (p - 2) * softMaxDeriv ε x ≤ 4 * M ^ (p - 2) := by
    calc softMax ε x ^ (p - 2) * softMaxDeriv ε x ≤ softMax ε x ^ (p - 2) * 1 :=
          mul_le_mul_of_nonneg_left hd1 hm0
      _ ≤ 4 * M ^ (p - 2) := by rw [mul_one]; exact h1.trans h3
  have hq : 0 ≤ p * (1 - p) := mul_nonneg hp0.le (by linarith)
  unfold testFunDeriv2
  have : p * (p - 1) * (softMax ε x ^ (p - 2) * softMaxDeriv ε x)
      = -(p * (1 - p) * (softMax ε x ^ (p - 2) * softMaxDeriv ε x)) := by ring
  rw [this, neg_le_neg_iff]
  calc p * (1 - p) * (softMax ε x ^ (p - 2) * softMaxDeriv ε x)
      ≤ p * (1 - p) * (4 * M ^ (p - 2)) := mul_le_mul_of_nonneg_left hprod hq
    _ = 4 * p * (1 - p) * M ^ (p - 2) := by ring

/-- **Generator inequality.** If `0 < p ≤ 1`, `0 < c` and `1 - p ≤ c / 8`, then
`g x · b x + ½ g' x ≥ (p/4) (max x ε)^{p-1} b x` for the regularized drift `b = regDrift c ε`. -/
theorem le_testFun_generator {c : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hc : 0 < c)
    (hpc : 1 - p ≤ c / 8) (hε : 0 < ε) (x : ℝ) :
    p / 4 * max x ε ^ (p - 1) * regDrift c ε x
      ≤ testFunDeriv p ε x * regDrift c ε x + 1 / 2 * testFunDeriv2 p ε x := by
  set M := max x ε
  have hM : 0 < M := hε.trans_le (le_max_right _ _)
  have hb : regDrift c ε x = c / M := rfl
  have hA := testFunDeriv_ge hp0 hp1 hε x
  have hB := testFunDeriv2_ge hp0 hp1 hε x
  have hbnn : 0 ≤ regDrift c ε x := regDrift_nonneg hc.le hε x
  have hMM : M ^ (p - 1) / M = M ^ (p - 2) := by
    rw [← Real.rpow_sub_one hM.ne']; ring_nf
  have hMp2 : 0 ≤ M ^ (p - 2) := (Real.rpow_pos_of_pos hM _).le
  have key : p / 2 * M ^ (p - 1) * regDrift c ε x = p * c / 2 * M ^ (p - 2) := by
    rw [hb, ← hMM]; field_simp
  have key4 : p / 4 * M ^ (p - 1) * regDrift c ε x = p * c / 4 * M ^ (p - 2) := by
    rw [hb, ← hMM]; field_simp
  have h1 : p / 2 * M ^ (p - 1) * regDrift c ε x ≤ testFunDeriv p ε x * regDrift c ε x :=
    mul_le_mul_of_nonneg_right hA hbnn
  have h2 : 4 * p * (1 - p) * M ^ (p - 2) ≤ p * c / 2 * M ^ (p - 2) := by
    apply mul_le_mul_of_nonneg_right _ hMp2
    nlinarith
  rw [key4]
  rw [key] at h1
  nlinarith

/-- The generator is nonnegative, and at least `(p/4) η^{p-1} b x` on `{x ≤ η}` when `ε ≤ η`. -/
theorem testFun_generator_ge_indicator {c η : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hc : 0 < c)
    (hpc : 1 - p ≤ c / 8) (hε : 0 < ε) (hεη : ε ≤ η) (x : ℝ) :
    p / 4 * η ^ (p - 1) * (Set.indicator (Set.Iic η) (regDrift c ε) x)
      ≤ testFunDeriv p ε x * regDrift c ε x + 1 / 2 * testFunDeriv2 p ε x := by
  have hgen := le_testFun_generator hp0 hp1 hc hpc hε x
  have hbnn : 0 ≤ regDrift c ε x := regDrift_nonneg hc.le hε x
  have hM : 0 < max x ε := hε.trans_le (le_max_right _ _)
  have hMp : 0 ≤ max x ε ^ (p - 1) := (Real.rpow_pos_of_pos hM _).le
  by_cases hx : x ∈ Set.Iic η
  · rw [Set.indicator_of_mem hx]
    have hmax : max x ε ≤ η := max_le hx hεη
    have : η ^ (p - 1) ≤ max x ε ^ (p - 1) := Real.rpow_le_rpow_of_nonpos hM hmax (by linarith)
    refine le_trans ?_ hgen
    apply mul_le_mul_of_nonneg_right _ hbnn
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · rw [Set.indicator_of_notMem hx, mul_zero]
    refine le_trans ?_ hgen
    positivity

/-! ### Bounds on the test function itself -/

theorem testFun_nonneg (hp0 : 0 < p) (hε : 0 < ε) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ testFun p ε x :=
  intervalIntegral.integral_nonneg hx fun s _ => (testFunDeriv_pos hp0 hε s).le

/-- `F y ≤ (max y 0)^p`. -/
theorem testFun_le (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) (y : ℝ) :
    testFun p ε y ≤ max y 0 ^ p := by
  rcases le_total y 0 with hy | hy
  · rw [max_eq_right hy, Real.zero_rpow hp0.ne']
    unfold testFun
    rw [intervalIntegral.integral_symm, neg_nonpos]
    exact intervalIntegral.integral_nonneg hy fun s _ => (testFunDeriv_pos hp0 hε s).le
  · rw [max_eq_left hy]
    have hint1 : IntervalIntegrable (testFunDeriv p ε) volume 0 y :=
      (continuous_testFunDeriv hε).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun s => p * s ^ (p - 1)) volume 0 y :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul p
    have hmono : ∫ s in (0 : ℝ)..y, testFunDeriv p ε s ≤ ∫ s in (0 : ℝ)..y, p * s ^ (p - 1) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hy hint1 hint2 fun s hs => ?_
      unfold testFunDeriv
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hs.1 (le_softMax hε s) (by linarith)) hp0.le
    have hval : ∫ s in (0 : ℝ)..y, p * s ^ (p - 1) = y ^ p := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
      rw [show p - 1 + 1 = p by ring, Real.zero_rpow hp0.ne', sub_zero]
      field_simp
    unfold testFun
    linarith

/-- `z^p ≤ 1 + z` for `z ≥ 0`, `0 ≤ p ≤ 1`. -/
theorem rpow_le_one_add {z : ℝ} (hz : 0 ≤ z) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : z ^ p ≤ 1 + z := by
  rcases le_total z 1 with h | h
  · linarith [Real.rpow_le_one hz h hp0]
  · have : z ^ p ≤ z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hp1
    rw [Real.rpow_one] at this
    linarith

end Bessel

end InteractingSLE
