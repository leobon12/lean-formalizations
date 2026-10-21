import SmallGammaGeodesics.Probes.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The band identity (4.4) and the telescoping identity (GA2 D4.6)

* `bandProbe_eq_band`: `B_{j,a} = ℓ_j ∫₀¹ y H''_{j,a} = ∑_k ρ(kℓ_j) b_k sin(kπa)` (4.4), for `y`
  continuous on `[0,1]`.
* `sum_band_eq_lowPass`: `∑_{j ≤ J} B_j = S_J`, from `∑_{j=0}^J ρ(kℓ_j) = χ(kℓ_J) - χ(2k) = χ(kℓ_J)`
  for integers `k ≥ 1`.

On the real line the probe is the real trigonometric polynomial `probeReal j a`
(`probeH_ofReal`), whose second derivative is `(2/ℓ) ∑ ρ(kℓ) sin(kπa) sin(kπ·)`
(`iteratedDeriv_two_probeReal`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset MeasureTheory
open scoped Real

namespace SmallGammaGeodesics

/-- The coefficient `ρ(kℓ_j) sin(kπa)/(kπ)²` of the probe `H_{j,a}`. -/
def probeCoef (j : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  rho ((k : ℝ) * ell j) * Real.sin ((k : ℝ) * π * a) / ((k : ℝ) * π) ^ 2

/-- The probe on the real line, as a real trigonometric polynomial. -/
def probeReal (j : ℕ) (a x : ℝ) : ℝ :=
  -(2 / ell j) * ∑ k ∈ Icc (1 : ℕ) (2 ^ (j + 1)), probeCoef j a k * Real.sin ((k : ℝ) * π * x)

theorem probeH_ofReal (j : ℕ) (a x : ℝ) : probeH j a x = (probeReal j a x : ℂ) := by
  unfold probeH probeReal probeCoef
  push_cast
  rfl

theorem probeH_ofReal_re (j : ℕ) (a x : ℝ) : (probeH j a x).re = probeReal j a x := by
  rw [probeH_ofReal, Complex.ofReal_re]

/-- `H_{j,a}(0) = 0`. -/
theorem probeH_zero (j : ℕ) (a : ℝ) : probeH j a 0 = 0 := by
  unfold probeH
  simp

/-- `H_{j,a}(1) = 0`. -/
theorem probeH_one (j : ℕ) (a : ℝ) : probeH j a 1 = 0 := by
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp, probeH_ofReal]
  unfold probeReal
  have : ∀ k ∈ Icc (1 : ℕ) (2 ^ (j + 1)), probeCoef j a k * Real.sin ((k : ℝ) * π * 1) = 0 := by
    intro k _
    rw [mul_one, Real.sin_nat_mul_pi, mul_zero]
  rw [sum_eq_zero this]
  simp

theorem hasDerivAt_sum_sin (s : Finset ℕ) (c ω : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (fun x => ∑ k ∈ s, c k * Real.sin (ω k * x))
      (∑ k ∈ s, c k * ω k * Real.cos (ω k * x)) x := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  exact ((((hasDerivAt_id' x).const_mul (ω k)).sin).const_mul (c k)).congr_deriv (by ring)

theorem hasDerivAt_sum_cos (s : Finset ℕ) (c ω : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (fun x => ∑ k ∈ s, c k * Real.cos (ω k * x))
      (∑ k ∈ s, -(c k * ω k * Real.sin (ω k * x))) x := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  exact ((((hasDerivAt_id' x).const_mul (ω k)).cos).const_mul (c k)).congr_deriv (by ring)

/-- Second derivative of a finite sine sum. -/
theorem iteratedDeriv_two_sum_sin (s : Finset ℕ) (c ω : ℕ → ℝ) (x : ℝ) :
    iteratedDeriv 2 (fun x => ∑ k ∈ s, c k * Real.sin (ω k * x)) x =
      -∑ k ∈ s, c k * ω k ^ 2 * Real.sin (ω k * x) := by
  have h1 : deriv (fun x => ∑ k ∈ s, c k * Real.sin (ω k * x)) =
      fun x => ∑ k ∈ s, (c k * ω k) * Real.cos (ω k * x) := by
    funext x
    exact (hasDerivAt_sum_sin s c ω x).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1,
    (hasDerivAt_sum_cos s (fun k => c k * ω k) ω x).deriv, ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  ring

theorem iteratedDeriv_two_probeReal (j : ℕ) (a t : ℝ) :
    iteratedDeriv 2 (probeReal j a) t =
      (2 / ell j) * ∑ k ∈ Icc (1 : ℕ) (2 ^ (j + 1)),
        rho ((k : ℝ) * ell j) * Real.sin ((k : ℝ) * π * a) * Real.sin ((k : ℝ) * π * t) := by
  have hfun : probeReal j a = fun x => -(2 / ell j) *
      ∑ k ∈ Icc (1 : ℕ) (2 ^ (j + 1)), probeCoef j a k * Real.sin (((k : ℝ) * π) * x) := by
    funext x
    rfl
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_two_sum_sin, mul_neg, neg_mul, neg_neg]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
  have hkπ : (k : ℝ) * π ≠ 0 := mul_ne_zero (by linarith) Real.pi_ne_zero
  unfold probeCoef
  field_simp

/-- **(4.4)**: `B_{j,a} = ℓ_j ∫₀¹ y H''_{j,a} = ∑_k ρ(kℓ_j) b_k sin(kπa)`. -/
theorem bandProbe_eq_band (y : ℝ → ℝ) (hy : ContinuousOn y (Set.Icc 0 1)) (j : ℕ) (a : ℝ) :
    bandProbe y j a = band y j a := by
  have hfun : (fun x : ℝ => (probeH j a x).re) = probeReal j a := by
    funext x
    exact probeH_ofReal_re j a x
  have hint : ∀ k ∈ Icc (1 : ℕ) (2 ^ (j + 1)),
      IntervalIntegrable (fun t => (2 / ell j) * (rho ((k : ℝ) * ell j) *
        Real.sin ((k : ℝ) * π * a)) * (y t * Real.sin ((k : ℝ) * π * t))) volume 0 1 := by
    intro k _
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_const.mul (hy.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousOn)
  unfold bandProbe band sineCoef
  rw [hfun]
  have hpt : ∀ t, y t * iteratedDeriv 2 (probeReal j a) t =
      ∑ k ∈ Icc (1 : ℕ) (2 ^ (j + 1)), (2 / ell j) * (rho ((k : ℝ) * ell j) *
        Real.sin ((k : ℝ) * π * a)) * (y t * Real.sin ((k : ℝ) * π * t)) := by
    intro t
    rw [iteratedDeriv_two_probeReal, mul_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum hint, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have := ell_pos j
  field_simp

/-! ### Telescoping -/

/-- `∑_{j=0}^J ρ(kℓ_j) = χ(kℓ_J) - χ(2k)`. -/
theorem sum_rho_eq (x : ℝ) (J : ℕ) :
    ∑ j ∈ range (J + 1), rho (x * ell j) = chi (x * ell J) - chi (2 * x) := by
  induction J with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, ell_zero, mul_one]
    unfold rho
    ring_nf
  | succ J ih =>
    rw [sum_range_succ, ih]
    unfold rho
    rw [show 2 * (x * ell (J + 1)) = x * ell J by rw [← two_mul_ell_succ J]; ring]
    ring

/-- For integers `k ≥ 1`: `∑_{j=0}^J ρ(kℓ_j) = χ(kℓ_J)`. -/
theorem sum_rho_natCast_eq {k : ℕ} (hk : 1 ≤ k) (J : ℕ) :
    ∑ j ∈ range (J + 1), rho ((k : ℝ) * ell j) = chi ((k : ℝ) * ell J) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [sum_rho_eq, chi_of_two_le (s := 2 * (k : ℝ)) (by linarith), sub_zero]

/-- Extending a band sum to a longer frequency range. -/
theorem band_eq_sum_Icc (y : ℝ → ℝ) {j J : ℕ} (hjJ : j ≤ J) (t : ℝ) :
    band y j t = ∑ k ∈ Icc (1 : ℕ) (2 ^ (J + 1)),
      rho ((k : ℝ) * ell j) * sineCoef y k * Real.sin ((k : ℝ) * π * t) := by
  unfold band
  refine sum_subset ?_ ?_
  · intro k hk
    simp only [mem_Icc] at hk ⊢
    exact ⟨hk.1, le_trans hk.2 (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
  · intro k hk1 hk
    simp only [mem_Icc, not_and_or, not_le] at hk hk1
    rcases hk with hk | hk
    · omega
    · rw [rho_of_two_le (two_le_natCast_mul_ell hk.le)]
      ring

/-- **Telescoping (GA2 D4.6)**: `∑_{j ≤ J} B_j = S_J`. -/
theorem sum_band_eq_lowPass (y : ℝ → ℝ) (J : ℕ) (t : ℝ) :
    ∑ j ∈ Finset.range (J + 1), band y j t = lowPass y J t := by
  have h1 : ∑ j ∈ range (J + 1), band y j t = ∑ j ∈ range (J + 1),
      ∑ k ∈ Icc (1 : ℕ) (2 ^ (J + 1)),
        rho ((k : ℝ) * ell j) * sineCoef y k * Real.sin ((k : ℝ) * π * t) := by
    refine sum_congr rfl fun j hj => ?_
    exact band_eq_sum_Icc y (j := j) (J := J) (by simp only [mem_range] at hj; omega) t
  rw [h1, sum_comm]
  unfold lowPass
  refine sum_congr rfl fun k hk => ?_
  rw [← sum_mul, ← sum_mul, sum_rho_natCast_eq (mem_Icc.mp hk).1]

end SmallGammaGeodesics
