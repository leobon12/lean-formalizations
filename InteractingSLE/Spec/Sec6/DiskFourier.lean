/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier coefficients of harmonic functions on the unit disk

Packet PROVE-SEC6-A (specification §6.1, proof of Aux. lemma 28, `source/spec/p145-192.md`,
`#aux-28-proof`, p. 163): "Write the harmonic Fourier expansion `u(re^{it}) = ∑ c_n r^{|n|} e^{int}`.
Taking `r = 1 − 1/|n|` in the coefficient bound … shows `|c_n| = O(|n|^α)`. Thus these coefficients
define a distribution `T` on the circle, and `u` is its Poisson extension. The radial functions
`u(re^{it})` converge to `T` in the distributional sense."

For `u` harmonic on the unit disk we write `u = Re F` with `F` holomorphic
(`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`) and expand `F` in its Taylor
series. This gives coefficients `c : ℤ → ℂ` with

  `u(re^{it}) = ∑_{n ∈ ℤ} c_n r^{|n|} e^{int}`, absolutely convergent for `0 ≤ r < 1`.

Pairing with a continuous `ψ : ℝ → ℂ` on `[0, 2π]` (`circCoeff ψ n = (2π)⁻¹ ∫₀^{2π} e^{-int} ψ`):

  `(2π)⁻¹ ∫₀^{2π} u(re^{it}) ψ(t) dt = ∑ c_n r^{|n|} ψ̂(−n)`.

## Main results

* `InteractingSLE.Sec6.circCoeff`: the Fourier coefficient on `[0, 2π]`;
* `InteractingSLE.Sec6.exists_disk_fourier`: the expansion of a harmonic function;
* `InteractingSLE.Sec6.hasSum_pairing`: the pairing identity;
* `InteractingSLE.Sec6.coeff_mul_pow_eq`: `c_n r^{|n|} = (2π)⁻¹ ∫₀^{2π} u(re^{it}) e^{−int} dt`.
-/

noncomputable section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ComplexConjugate

namespace InteractingSLE.Sec6

/-! ## Fourier coefficients on `[0, 2π]` -/

/-- The `n`-th Fourier coefficient of `ψ` on `[0, 2π]`: `(2π)⁻¹ ∫₀^{2π} e^{−int} ψ(t) dt`. -/
def circCoeff (ψ : ℝ → ℂ) (n : ℤ) : ℂ :=
  ((2 * π)⁻¹ : ℝ) * ∫ t in (0 : ℝ)..2 * π, exp (-(n * t * I)) * ψ t

/-- The point `r e^{it}`. -/
abbrev polarPt (r t : ℝ) : ℂ := (r : ℂ) * exp (t * I)

theorem norm_polarPt {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : ‖polarPt r t‖ = r := by
  simp [polarPt, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr]

theorem polarPt_mem_ball {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    polarPt r t ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_polarPt hr0]; exact hr1

/-! ## Taylor coefficients -/

/-- The Taylor coefficients of `F` at `0`. -/
def taylorCoeff (F : ℂ → ℂ) (k : ℕ) : ℂ := (k.factorial : ℂ)⁻¹ * iteratedDeriv k F 0

theorem hasSum_taylorCoeff {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) : HasSum (fun k => taylorCoeff F k * z ^ k) (F z) := by
  have h := Complex.hasSum_taylorSeries_on_ball hF hz
  simp only [sub_zero, smul_eq_mul] at h
  refine h.congr_fun fun k => ?_
  simp only [taylorCoeff]; ring

/-- Absolute convergence of the Taylor series inside the disk. -/
theorem summable_norm_taylorCoeff_mul_pow {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k => ‖taylorCoeff F k‖ * r ^ k := by
  obtain ⟨ρ, hrρ, hρ1⟩ := exists_between hr1
  have hρ0 : 0 < ρ := lt_of_le_of_lt hr0 hrρ
  have hs := (hasSum_taylorCoeff hF (z := (ρ : ℂ)) (by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1)).summable
  obtain ⟨M, hM⟩ : BddAbove (range fun k => ‖taylorCoeff F k * (ρ : ℂ) ^ k‖) :=
    hs.tendsto_atTop_zero.norm.bddAbove_range
  have hq0 : 0 ≤ r / ρ := div_nonneg hr0 hρ0.le
  have hq1 : r / ρ < 1 := (div_lt_one hρ0).2 hrρ
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left M)
  have hk := hM ⟨k, rfl⟩
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0] at hk
  calc ‖taylorCoeff F k‖ * r ^ k = (‖taylorCoeff F k‖ * ρ ^ k) * (r / ρ) ^ k := by
        rw [div_pow, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (pow_pos hρ0 k).ne']
    _ ≤ M * (r / ρ) ^ k := mul_le_mul_of_nonneg_right hk (by positivity)

/-! ## The harmonic Fourier expansion -/

/-- The harmonic Fourier coefficients of `Re F`: `a_n / 2` for `n > 0`, `conj a_{|n|} / 2` for
`n < 0` and `Re a_0` for `n = 0`, where `a_k` are the Taylor coefficients of `F` at `0`. -/
def diskCoeff (F : ℂ → ℂ) (n : ℤ) : ℂ :=
  if 0 < n then taylorCoeff F n.natAbs / 2
  else if n < 0 then conj (taylorCoeff F n.natAbs) / 2
  else ((taylorCoeff F 0).re : ℂ)

theorem norm_diskCoeff_le (F : ℂ → ℂ) (n : ℤ) :
    ‖diskCoeff F n‖ ≤ ‖taylorCoeff F n.natAbs‖ := by
  unfold diskCoeff
  split_ifs with h1 h2
  · rw [norm_div]; simp only [RCLike.norm_ofNat]; linarith [norm_nonneg (taylorCoeff F n.natAbs)]
  · rw [norm_div, Complex.norm_conj]; simp only [RCLike.norm_ofNat]
    linarith [norm_nonneg (taylorCoeff F n.natAbs)]
  · have : n = 0 := by omega
    subst this
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _

theorem polarPt_pow (r t : ℝ) (k : ℕ) :
    polarPt r t ^ k = (r : ℂ) ^ k * exp (((k : ℤ) : ℂ) * t * I) := by
  rw [polarPt, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  push_cast; ring

theorem summable_norm_diskCoeff_mul_pow {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℤ => ‖diskCoeff F n‖ * r ^ n.natAbs := by
  have hs := summable_norm_taylorCoeff_mul_pow hF hr0 hr1
  have hs' : Summable fun n : ℤ => ‖taylorCoeff F n.natAbs‖ * r ^ n.natAbs :=
    Summable.of_nat_of_neg (by simpa using hs) (by simpa using hs)
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (norm_diskCoeff_le F n) (by positivity)) hs'

/-- The real part of a holomorphic function on the disk, expanded in polar coordinates:
`Re F(re^{it}) = ∑_{n ∈ ℤ} c_n r^{|n|} e^{int}`. -/
theorem hasSum_diskCoeff {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    HasSum (fun n : ℤ => diskCoeff F n * (r : ℂ) ^ n.natAbs * exp (n * t * I))
      ((F (polarPt r t)).re : ℂ) := by
  have hT := hasSum_taylorCoeff hF (polarPt_mem_ball hr0 hr1 t)
  -- the nonnegative indices
  have hA : HasSum (fun k : ℕ => diskCoeff F k * (r : ℂ) ^ (k : ℤ).natAbs * exp ((k : ℤ) * t * I))
      (F (polarPt r t) / 2 + (((taylorCoeff F 0).re : ℂ) - taylorCoeff F 0 / 2)) := by
    have h1 := (hT.div_const 2).add (hasSum_ite_eq 0 (((taylorCoeff F 0).re : ℂ) -
      taylorCoeff F 0 / 2))
    refine h1.congr_fun fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [diskCoeff]
    · have hk' : (0 : ℤ) < k := by exact_mod_cast hk
      simp only [diskCoeff, hk', ↓reduceIte, Int.natAbs_natCast, hk.ne', polarPt_pow]
      ring
  -- the negative indices
  have hB : HasSum (fun k : ℕ => diskCoeff F (-((k : ℤ) + 1)) * (r : ℂ) ^ (-((k : ℤ) + 1)).natAbs *
      exp ((-((k : ℤ) + 1) : ℤ) * t * I)) (conj (F (polarPt r t) - taylorCoeff F 0) / 2) := by
    have h0 : HasSum (fun k : ℕ => taylorCoeff F (k + 1) * polarPt r t ^ (k + 1))
        (F (polarPt r t) - taylorCoeff F 0) := by
      have := (hasSum_nat_add_iff' 1).2 hT
      simpa using this
    have h1 := (Complex.hasSum_conj'.2 h0).div_const 2
    refine h1.congr_fun fun k => ?_
    have hneg : -((k : ℤ) + 1) < 0 := by omega
    have hnpos : ¬ (0 < -((k : ℤ) + 1)) := by omega
    have habs : (-((k : ℤ) + 1)).natAbs = k + 1 := by omega
    simp only [diskCoeff, hnpos, hneg, ↓reduceIte, habs, polarPt_pow, map_mul, map_pow,
      Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I, map_intCast]
    push_cast; ring_nf
  have hsum := HasSum.of_nat_of_neg_add_one
    (f := fun n : ℤ => diskCoeff F n * (r : ℂ) ^ n.natAbs * exp (n * t * I)) hA hB
  convert hsum using 1
  rw [map_sub, Complex.re_eq_add_conj, Complex.re_eq_add_conj (taylorCoeff F 0)]
  ring

/-! ## Pairing with continuous functions -/

/-- **Pairing identity.** For `u = Re F` on the disk and `ψ` continuous,
`(2π)⁻¹ ∫₀^{2π} u(re^{it}) ψ(t) dt = ∑ c_n r^{|n|} ψ̂(−n)`. -/
theorem hasSum_pairing {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1)) {u : ℂ → ℝ}
    (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z) {ψ : ℝ → ℂ} (hψ : Continuous ψ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℤ => diskCoeff F n * (r : ℂ) ^ n.natAbs * circCoeff ψ (-n))
      (((2 * π)⁻¹ : ℝ) * ∫ t in (0 : ℝ)..2 * π, (u (polarPt r t) : ℂ) * ψ t) := by
  -- the continuous summands
  let f : ℤ → C(ℝ, ℂ) := fun n =>
    ⟨fun t => diskCoeff F n * (r : ℂ) ^ n.natAbs * exp (n * t * I) * ψ t, by fun_prop⟩
  obtain ⟨M, hM⟩ : ∃ M, ∀ t ∈ uIcc (0 : ℝ) (2 * π), ‖ψ t‖ ≤ M :=
    (isCompact_uIcc.exists_bound_of_continuousOn hψ.continuousOn)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (left_mem_uIcc))
  have hsum : Summable fun n : ℤ =>
      ‖(f n).restrict (⟨uIcc (0 : ℝ) (2 * π), isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_norm_diskCoeff_mul_pow hF hr0 hr1).mul_right M)
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk, f, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    have : ‖exp (((n : ℤ) : ℂ) * (t : ℝ) * I)‖ = 1 := by
      rw [show ((n : ℤ) : ℂ) * (t : ℝ) * I = (((n : ℝ) * t : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [this, mul_one]
    exact mul_le_mul_of_nonneg_left (hM t t.2) (by positivity)
  have hI := intervalIntegral.hasSum_intervalIntegral_of_summable_norm (a := 0) (b := 2 * π) hsum
  have hpt : ∀ t : ℝ, ∑' n : ℤ, f n t = (u (polarPt r t) : ℂ) * ψ t := by
    intro t
    have h := (hasSum_diskCoeff hF hr0 hr1 t).mul_right (ψ t)
    rw [hu _ (polarPt_mem_ball hr0 hr1 t)] at h
    exact h.tsum_eq
  simp_rw [hpt] at hI
  have h2 := hI.mul_left (((2 * π)⁻¹ : ℝ) : ℂ)
  refine h2.congr_fun fun n => ?_
  simp only [f, ContinuousMap.coe_mk, circCoeff, Int.cast_neg, neg_mul, neg_neg]
  have : (fun t : ℝ => diskCoeff F n * (r : ℂ) ^ n.natAbs * exp (n * (t : ℂ) * I) * ψ t) =
      fun t : ℝ => diskCoeff F n * (r : ℂ) ^ n.natAbs * (exp (n * (t : ℂ) * I) * ψ t) := by
    funext t; ring
  rw [this, intervalIntegral.integral_const_mul]
  ring

/-! ## Coefficients -/

/-- Orthogonality of the exponentials on `[0, 2π]`. -/
theorem circCoeff_exp_neg (m n : ℤ) :
    circCoeff (fun t : ℝ => exp (-((m : ℂ) * t * I))) (-n) = if n = m then 1 else 0 := by
  unfold circCoeff
  have hcomb : ∀ t : ℝ, exp (-(((-n : ℤ) : ℂ) * t * I)) * exp (-((m : ℂ) * t * I)) =
      exp ((((n : ℂ) - m) * I) * t) := by
    intro t; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [hcomb]
  split_ifs with h
  · subst h
    simp only [sub_self, zero_mul, Complex.exp_zero, intervalIntegral.integral_const, sub_zero,
      Complex.real_smul, mul_one]
    push_cast
    field_simp
  · have hc : ((n : ℂ) - m) * I ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      rw [sub_ne_zero]; exact_mod_cast h
    rw [integral_exp_mul_complex hc]
    have h2 : exp (((n : ℂ) - m) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [show ((n : ℂ) - m) * I * ((2 * π : ℝ) : ℂ) = ((n - m : ℤ) : ℂ) * (2 * π * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    push_cast at h2
    simp [h2]

/-- **The coefficient formula.** `c_n r^{|n|} = (2π)⁻¹ ∫₀^{2π} u(re^{it}) e^{−int} dt`. -/
theorem diskCoeff_mul_pow_eq {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1)) {u : ℂ → ℝ}
    (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℤ) :
    diskCoeff F n * (r : ℂ) ^ n.natAbs =
      ((2 * π)⁻¹ : ℝ) * ∫ t in (0 : ℝ)..2 * π, (u (polarPt r t) : ℂ) * exp (-((n : ℂ) * t * I)) := by
  have h := hasSum_pairing hF hu (ψ := fun t : ℝ => exp (-((n : ℂ) * t * I))) (by fun_prop) hr0 hr1
  simp_rw [circCoeff_exp_neg] at h
  have h' : HasSum (fun m : ℤ => if m = n then diskCoeff F n * (r : ℂ) ^ n.natAbs else 0)
      (diskCoeff F n * (r : ℂ) ^ n.natAbs) := hasSum_ite_eq n _
  refine h'.unique (h.congr_fun fun m => ?_)
  split_ifs with hm
  · subst hm; ring
  · ring

/-- The circle bound: `‖c_n‖ r^{|n|} ≤ sup_{|z| = r} |u|`. -/
theorem norm_diskCoeff_mul_pow_le {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    {u : ℂ → ℝ} (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z) {r M : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hM : ∀ t : ℝ, |u (polarPt r t)| ≤ M) (n : ℤ) :
    ‖diskCoeff F n‖ * r ^ n.natAbs ≤ M := by
  have h := congrArg norm (diskCoeff_mul_pow_eq hF hu hr0 hr1 n)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at h
  rw [h, norm_mul]
  have hI : ‖∫ t in (0 : ℝ)..2 * π, (u (polarPt r t) : ℂ) * exp (-((n : ℂ) * t * I))‖ ≤
      M * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖exp (-((n : ℂ) * t * I))‖ = 1 := by
      rw [show -((n : ℂ) * t * I) = ((-(n : ℝ) * t : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [this, mul_one]; exact hM t
  have hpi : 0 < 2 * π := by positivity
  rw [sub_zero, abs_of_pos hpi] at hI
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpi)]
  calc (2 * π)⁻¹ * ‖∫ t in (0 : ℝ)..2 * π, (u (polarPt r t) : ℂ) * exp (-((n : ℂ) * t * I))‖
      ≤ (2 * π)⁻¹ * (M * (2 * π)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = M := by field_simp

/-- `(m / (m + 1))^m ≥ e⁻¹`. -/
theorem exp_neg_one_le_pow (m : ℕ) : Real.exp (-1) ≤ ((m : ℝ) / (m + 1)) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero]; exact Real.exp_le_one_iff.2 (by norm_num)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 / (m : ℝ))
    calc (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp (1 / m) ^ m :=
          pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h2 : ((m : ℝ) / (m + 1)) ^ m = ((1 + 1 / (m : ℝ)) ^ m)⁻¹ := by
    rw [← inv_pow]; congr 1; field_simp
  rw [h2, Real.exp_neg]
  exact inv_anti₀ (by positivity) h1

/-- **Coefficient growth** (`|c_n| = O(|n|^α)`, proof of Aux. lemma 28): if
`|u(z)| ≤ C (1 − |z|)^{−α}` on the disk, then `‖c_n‖ ≤ e C (1 + |n|)^α`. -/
theorem norm_diskCoeff_le_of_growth {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    {u : ℂ → ℝ} (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z) {C α : ℝ}
    (hgrowth : ∀ z ∈ ball (0 : ℂ) 1, |u z| ≤ C * (1 - ‖z‖) ^ (-α)) (n : ℤ) :
    ‖diskCoeff F n‖ ≤ Real.exp 1 * C * (1 + |(n : ℝ)|) ^ α := by
  set m := n.natAbs with hm
  have hmR : |(n : ℝ)| = m := by rw [hm, Nat.cast_natAbs, Int.cast_abs]
  set r : ℝ := (m : ℝ) / (m + 1) with hr
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := (div_lt_one hm1).2 (by linarith)
  have h1r : 1 - r = ((m : ℝ) + 1)⁻¹ := by rw [hr]; field_simp; ring
  have hbound : ∀ t : ℝ, |u (polarPt r t)| ≤ C * ((m : ℝ) + 1) ^ α := by
    intro t
    have := hgrowth _ (polarPt_mem_ball hr0 hr1 t)
    rwa [norm_polarPt hr0, h1r, Real.rpow_neg (inv_nonneg.2 hm1.le), Real.inv_rpow hm1.le,
      inv_inv] at this
  have hc := norm_diskCoeff_mul_pow_le hF hu hr0 hr1 hbound n
  rw [← hm] at hc
  have hpow := exp_neg_one_le_pow m
  have hpos : 0 < r ^ m := lt_of_lt_of_le (Real.exp_pos _) hpow
  rw [hmR, add_comm]
  calc ‖diskCoeff F n‖ ≤ C * ((m : ℝ) + 1) ^ α / r ^ m := by rw [le_div_iff₀ hpos]; exact hc
    _ ≤ C * ((m : ℝ) + 1) ^ α / Real.exp (-1) := by
        have hC : 0 ≤ C * ((m : ℝ) + 1) ^ α := le_trans (by positivity) (hbound 0)
        exact div_le_div_of_nonneg_left hC (Real.exp_pos _) hpow
    _ = Real.exp 1 * C * ((m : ℝ) + 1) ^ α := by rw [Real.exp_neg]; field_simp

/-! ## Derivatives, Parseval, and the `H¹` bound -/

theorem hasDerivAt_exp_neg_mul_I (n : ℤ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => exp (-((n : ℂ) * t * I))) (-((n : ℂ) * I) * exp (-((n : ℂ) * t * I)))
      t := by
  have h : HasDerivAt (fun w : ℂ => -((n : ℂ) * w * I)) (-((n : ℂ) * 1 * I)) (t : ℂ) :=
    (((hasDerivAt_id (t : ℂ)).const_mul (n : ℂ)).mul_const I).neg
  have h2 := (h.cexp).comp_ofReal
  simp only [mul_one] at h2
  convert h2 using 1; ring

/-- **Derivative rule.** For a `C¹` function with `ψ(2π) = ψ(0)`, `ψ'̂(n) = i n ψ̂(n)`. -/
theorem circCoeff_deriv {ψ ψ' : ℝ → ℂ} (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : Continuous ψ')
    (hper : ψ (2 * π) = ψ 0) (n : ℤ) : circCoeff ψ' n = ((n : ℂ) * I) * circCoeff ψ n := by
  have hcont : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hψ t).continuousAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * π)
    (fun t _ => hasDerivAt_exp_neg_mul_I n t) (fun t _ => hψ t)
    ((by fun_prop : Continuous fun t : ℝ => -((n : ℂ) * I) * exp (-((n : ℂ) * t * I))).intervalIntegrable _ _)
    (hψ'.intervalIntegrable _ _)
  have hend : exp (-((n : ℂ) * ((2 * π : ℝ) : ℂ) * I)) = 1 := by
    rw [show -((n : ℂ) * ((2 * π : ℝ) : ℂ) * I) = ((-n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  unfold circCoeff
  rw [hparts, hend, hper]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul, sub_self,
    zero_sub]
  have : (fun t : ℝ => -((n : ℂ) * I) * exp (-((n : ℂ) * t * I)) * ψ t) =
      fun t : ℝ => -((n : ℂ) * I) * (exp (-((n : ℂ) * t * I)) * ψ t) := by funext t; ring
  rw [this, intervalIntegral.integral_const_mul]
  ring

/-- `circCoeff` is Mathlib's `fourierCoeffOn` on `[0, 2π]`. -/
theorem circCoeff_eq_fourierCoeffOn (ψ : ℝ → ℂ) (n : ℤ) :
    circCoeff ψ n = fourierCoeffOn Real.two_pi_pos ψ n := by
  rw [fourierCoeffOn_eq_integral, circCoeff]
  simp only [sub_zero, one_div, Complex.real_smul, smul_eq_mul]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [fourier_coe_apply]
  congr 2
  push_cast
  field_simp
  ring

/-- **Parseval** on `[0, 2π]`. -/
theorem hasSum_sq_circCoeff {φ : ℝ → ℂ} (hφ : Continuous φ) :
    HasSum (fun n => ‖circCoeff φ n‖ ^ 2) ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖φ t‖ ^ 2) := by
  have hL2 : MemLp φ 2 (volume.restrict (Ioc 0 (2 * π))) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
      hφ.continuousOn
    refine MemLp.of_bound hφ.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hC t (Ioc_subset_Icc_self ht)
  have h := hasSum_sq_fourierCoeffOn Real.two_pi_pos hL2
  simp only [sub_zero, smul_eq_mul] at h
  simp_rw [circCoeff_eq_fourierCoeffOn]
  exact h

/-- The weight `(1 + |n|)^{2α} / n²`, set to `0` at `n = 0`. -/
def sobWeight (α : ℝ) (n : ℤ) : ℝ := if n = 0 then 0 else (1 + |(n : ℝ)|) ^ (2 * α) / (n : ℝ) ^ 2

theorem sobWeight_nonneg (α : ℝ) (n : ℤ) : 0 ≤ sobWeight α n := by
  unfold sobWeight; split_ifs <;> positivity

theorem summable_sobWeight {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1 / 2) : Summable (sobWeight α) := by
  have hb : (1 : ℝ) < 2 - 2 * α := by linarith
  refine Summable.of_nonneg_of_le (sobWeight_nonneg α) (fun n => ?_)
    ((Real.summable_abs_int_rpow hb).mul_left ((2 : ℝ) ^ (2 * α)))
  unfold sobWeight
  split_ifs with hn
  · positivity
  have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  have hpos : 0 < |(n : ℝ)| := by linarith
  have h1 : (1 + |(n : ℝ)|) ^ (2 * α) ≤ (2 * |(n : ℝ)|) ^ (2 * α) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have h2 : (2 * |(n : ℝ)|) ^ (2 * α) / (n : ℝ) ^ 2 = (2 : ℝ) ^ (2 * α) * |(n : ℝ)| ^ (-(2 - 2 * α)) := by
    rw [Real.mul_rpow (by norm_num) hpos.le, ← sq_abs (n : ℝ), mul_div_assoc]
    congr 1
    rw [show -(2 - 2 * α) = 2 * α - (2 : ℕ) by push_cast; ring, Real.rpow_sub hpos,
      Real.rpow_natCast]
  calc (1 + |(n : ℝ)|) ^ (2 * α) / (n : ℝ) ^ 2 ≤ (2 * |(n : ℝ)|) ^ (2 * α) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ = _ := h2

/-- **The `H¹` bound for the pairing** (the coefficients define a distribution of order `< 1`):
if `‖c_n‖ ≤ K (1 + |n|)^α` with `0 ≤ α < 1/2`, then for a `C¹` function `φ` with
`φ(2π) = φ(0)` and every `ε > 0`, the series `∑ ‖c_n‖ ‖φ̂(−n)‖` converges, and
`∑ ‖c_n‖ ‖φ̂(−n)‖ ≤ ‖c_0‖ ‖φ̂(0)‖ + (K/2) (ε ∑ w_n + ε⁻¹ (2π)⁻¹ ∫₀^{2π} ‖φ'‖²)`. -/
theorem pairing_bound {c : ℤ → ℂ} {K α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1 / 2)
    (hc : ∀ n, ‖c n‖ ≤ K * (1 + |(n : ℝ)|) ^ α) {φ φ' : ℝ → ℂ}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : Continuous φ') (hper : φ (2 * π) = φ 0)
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n => ‖c n‖ * ‖circCoeff φ (-n)‖) ∧
      ∑' n, ‖c n‖ * ‖circCoeff φ (-n)‖ ≤ ‖c 0‖ * ‖circCoeff φ 0‖ +
        K / 2 * (ε * ∑' n, sobWeight α n +
          ε⁻¹ * ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖φ' t‖ ^ 2)) := by
  have hK : 0 ≤ K := by
    have h0 := hc 0
    simp only [Int.cast_zero, abs_zero, add_zero, Real.one_rpow, mul_one] at h0
    linarith [norm_nonneg (c 0)]
  have hP := hasSum_sq_circCoeff hφ'
  have hPneg : HasSum (fun n : ℤ => ‖circCoeff φ' (-n)‖ ^ 2)
      ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖φ' t‖ ^ 2) :=
    (Equiv.neg ℤ).hasSum_iff.2 hP
  let g : ℤ → ℝ := fun n => (if n = 0 then ‖c 0‖ * ‖circCoeff φ 0‖ else 0) +
      K / 2 * (ε * sobWeight α n + ε⁻¹ * ‖circCoeff φ' (-n)‖ ^ 2)
  have hg : HasSum g (‖c 0‖ * ‖circCoeff φ 0‖ + K / 2 * (ε * ∑' n, sobWeight α n +
      ε⁻¹ * ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖φ' t‖ ^ 2))) :=
    (hasSum_ite_eq 0 _).add
      ((((summable_sobWeight hα0 hα).hasSum.mul_left ε).add (hPneg.mul_left ε⁻¹)).mul_left (K / 2))
  have hle : ∀ n, ‖c n‖ * ‖circCoeff φ (-n)‖ ≤ g n := by
    intro n
    have hrest : 0 ≤ K / 2 * (ε * sobWeight α n + ε⁻¹ * ‖circCoeff φ' (-n)‖ ^ 2) := by
      have := sobWeight_nonneg α n
      positivity
    by_cases hn : n = 0
    · subst hn
      simp only [g, neg_zero, ↓reduceIte] at hrest ⊢
      linarith
    · simp only [g, hn, ↓reduceIte, zero_add]
      have hnpos : 0 < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
      have hd := circCoeff_deriv hφ hφ' hper (-n)
      have hnorm : ‖circCoeff φ' (-n)‖ = |(n : ℝ)| * ‖circCoeff φ (-n)‖ := by
        rw [hd, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, Int.cast_neg,
          abs_neg]
      set a := (1 + |(n : ℝ)|) ^ α / |(n : ℝ)| with ha
      set b := ‖circCoeff φ' (-n)‖ with hb
      have ha2 : a ^ 2 = sobWeight α n := by
        rw [ha, sobWeight]
        simp only [hn, ↓reduceIte]
        rw [div_pow, sq_abs, ← Real.rpow_mul_natCast (by positivity)]
        congr 2; push_cast; ring
      have hφn : ‖circCoeff φ (-n)‖ = b / |(n : ℝ)| := by
        rw [hnorm]; field_simp
      have hamgm : a * b ≤ (ε * a ^ 2 + ε⁻¹ * b ^ 2) / 2 := by
        have h1 : 0 ≤ ε⁻¹ * (ε * a - b) ^ 2 := by positivity
        have h2 : ε⁻¹ * (ε * a - b) ^ 2 = ε * a ^ 2 + ε⁻¹ * b ^ 2 - 2 * (a * b) := by
          field_simp; ring
        linarith
      calc ‖c n‖ * ‖circCoeff φ (-n)‖ ≤ K * (1 + |(n : ℝ)|) ^ α * (b / |(n : ℝ)|) := by
            rw [hφn]; exact mul_le_mul_of_nonneg_right (hc n) (by positivity)
        _ = K * (a * b) := by rw [ha]; ring
        _ ≤ K * ((ε * a ^ 2 + ε⁻¹ * b ^ 2) / 2) := mul_le_mul_of_nonneg_left hamgm hK
        _ = K / 2 * (ε * sobWeight α n + ε⁻¹ * b ^ 2) := by rw [ha2]; ring
  have hsum : Summable (fun n => ‖c n‖ * ‖circCoeff φ (-n)‖) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hg.summable
  exact ⟨hsum, hasSum_le hle hsum.hasSum hg⟩

end InteractingSLE.Sec6
