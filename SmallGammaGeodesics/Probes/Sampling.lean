import SmallGammaGeodesics.Probes.Bands
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Lemma 4.1, (4.5): deterministic sampling sets for the bands

For a real sine polynomial `f(x) = ∑_{k=1}^N c_k sin(kπx)` and the grid `a_i = 2i/(3N)`,
`i < 3N`, we prove `|f(x)| ≤ (7/4) max_i |f(a_i)|` for every real `x` (`sinePoly_le_grid`).

The proof is a discrete reproducing-kernel argument, with finite sums only (no Bernstein
inequality, no integrals; ruling G13):

* **Reproduction** (`sinePoly_reproduce`): `f(x) = (3N)⁻¹ ∑_i f(a_i) V_N(x - a_i)` with
  `V_N(y) = N⁻¹ ∑_{r<3N} ∑_{r'<N} e^{iπ(r-r'-N)y} = N⁻¹ D_{3N}(y) conj(D_N(y)) e^{-iπNy}`, where
  `D_K(y) = ∑_{r<K} e^{iπry}`. Its Fourier coefficients equal `1` on `|m| ≤ N` and vanish for
  `|m| ≥ 2N`. Reproduction follows from the grid orthogonality
  `∑_{i<M} e^{iπν·2i/M} = M·[M ∣ ν]` (`sum_range_ex_grid`).
* **Lebesgue constant** (`sum_norm_sampKernel_le`): discrete Parseval
  `∑_i |D_K(x-a_i)|² = 3N·K` for `K ≤ 3N` (`sum_normSq_dirichletSum`) and
  `|D_{3N}||D_N| ≤ |D_{3N}|²/4 + |D_N|²` give `(3N)⁻¹ ∑_i |V_N(x-a_i)| ≤ 7/4`.

For the band `B_j` (degree `N = 2^{j+1}`), oddness and 2-periodicity reduce the grid to
`A_j = {i/(3·2^j) : 0 ≤ i ≤ 3·2^j} ⊆ [0,1]`, of size `3·2^j + 1 ≤ 4/ℓ_j` (`lemma41_sampling`).
This proves (4.5) without GA2 D4.4's weak Bernstein inequality: the grid has mesh `ℓ_j/3` and
the factor is `7/4`.

The same kernel also gives D4.4's **weak Bernstein inequality**. Differentiating the reproduction
gives `f' = (3N)⁻¹ ∑_i f(a_i) V_N'(· - a_i)` (`deriv_sinePoly_eq`), and
`∑_i |V_N'(x - a_i)| ≤ (35π/2) N · 3N` follows from weighted discrete Parseval
(`sum_normSq_weightedSum`) and AM–GM. Hence `|f'| ≤ (35π/2) N sup|f|` (`abs_deriv_sinePoly_le`),
and for the bands `|B_j(s) - B_j(t)| ≤ 35π sup|B_j| min(1, |s-t|/ℓ_j)` (`band_holder`; GA3
X7(f), used for (6.5)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset
open scoped Real ComplexConjugate

namespace SmallGammaGeodesics

/-! ### Exponentials -/

/-- `e(t) = exp(it)` for real `t`. -/
def ex (t : ℝ) : ℂ := Complex.exp (t * Complex.I)

theorem ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  unfold ex
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ex_zero : ex 0 = 1 := by simp [ex]

theorem norm_ex (t : ℝ) : ‖ex t‖ = 1 := Complex.norm_exp_ofReal_mul_I t

theorem conj_ex (t : ℝ) : conj (ex t) = ex (-t) := by
  unfold ex
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem ex_mul_ex_neg (t : ℝ) : ex t * ex (-t) = 1 := by
  rw [← ex_add, add_neg_cancel, ex_zero]

theorem ofReal_sin_eq_ex (t : ℝ) :
    (Real.sin t : ℂ) = (ex t - ex (-t)) / (2 * Complex.I) := by
  rw [Complex.ofReal_sin]
  unfold ex
  rw [eq_div_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero), Complex.sin]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### Grid orthogonality -/

/-- `∑_{i<M} e^{iπν·2i/M} = M` if `M ∣ ν`, and `0` otherwise. -/
theorem sum_range_ex_grid {M : ℕ} (hM : 0 < M) (ν : ℤ) :
    ∑ i ∈ range M, ex (π * ν * (2 * i / M)) = if (M : ℤ) ∣ ν then (M : ℂ) else 0 := by
  have hM0 : M ≠ 0 := hM.ne'
  have hζ := Complex.isPrimitiveRoot_exp M hM0
  set ζ := Complex.exp (2 * π * Complex.I / M) with hζdef
  have hpow : ∀ i : ℕ, ex (π * ν * (2 * i / M)) = (ζ ^ ν) ^ i := by
    intro i
    rw [hζdef, ← Complex.exp_int_mul, ← Complex.exp_nat_mul]
    unfold ex
    congr 1
    push_cast
    field_simp
  simp_rw [hpow]
  split_ifs with h
  · rw [(hζ.zpow_eq_one_iff_dvd ν).mpr h]
    simp
  · have hw1 : ζ ^ ν ≠ 1 := fun h1 => h ((hζ.zpow_eq_one_iff_dvd ν).mp h1)
    rw [geom_sum_eq hw1]
    have : (ζ ^ ν) ^ M = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [this, sub_self, zero_div]

/-- Grid orthogonality for small frequencies: for `|ν| < M`,
`∑_{i<M} e^{iπν·2i/M} = M·[ν = 0]`. -/
theorem sum_range_ex_grid_of_lt {M : ℕ} (hM : 0 < M) {ν : ℤ} (hν : |ν| < M) :
    ∑ i ∈ range M, ex (π * ν * (2 * i / M)) = if ν = 0 then (M : ℂ) else 0 := by
  rw [sum_range_ex_grid hM]
  congr 1
  apply propext
  constructor
  · rintro ⟨q, hq⟩
    rw [hq] at hν ⊢
    rcases eq_or_ne q 0 with h0 | h0
    · rw [h0, mul_zero]
    · exfalso
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ M)] at hν
      have : 1 ≤ |q| := Int.one_le_abs h0
      nlinarith
  · rintro rfl
    exact dvd_zero _

/-! ### Sine polynomials and the sampling kernel -/

/-- The real sine polynomial `f(x) = ∑_{k=1}^N c_k sin(kπx)`. -/
def sinePoly (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Icc (1 : ℕ) N, c k * Real.sin ((k : ℝ) * π * x)

/-- The grid point `a_i = 2i/(3N)`. -/
def gridPt (N i : ℕ) : ℝ := 2 * i / (3 * N : ℕ)

/-- `D_K(y) = ∑_{r<K} e^{iπry}`. -/
def dirichletSum (K : ℕ) (y : ℝ) : ℂ := ∑ r ∈ range K, ex (π * r * y)

/-- The sampling kernel `V_N(y) = N⁻¹ ∑_{r<3N} ∑_{r'<N} e^{iπ(r-r'-N)y}`. -/
def sampKernel (N : ℕ) (y : ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ r ∈ range (3 * N), ∑ r' ∈ range N, ex (π * ((r : ℝ) - r' - N) * y)

/-- Projection of a sine polynomial on one frequency, by grid orthogonality. -/
theorem sum_sinePoly_mul_ex {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (x : ℝ) (μ : ℤ)
    (hμ1 : -(2 * N : ℤ) < μ) (hμ2 : μ < 2 * N) :
    ∑ i ∈ range (3 * N), (sinePoly N c (gridPt N i) : ℂ) * ex (π * μ * (x - gridPt N i)) =
      (3 * N : ℕ) * ex (π * μ * x) / (2 * Complex.I) *
        ∑ k ∈ Icc (1 : ℕ) N, (c k : ℂ) *
          ((if (k : ℤ) = μ then 1 else 0) - (if -(k : ℤ) = μ then 1 else 0)) := by
  have hM : 0 < 3 * N := by omega
  -- expand the sine polynomial
  have hexp : ∀ i : ℕ, (sinePoly N c (gridPt N i) : ℂ) * ex (π * μ * (x - gridPt N i)) =
      ex (π * μ * x) / (2 * Complex.I) * ∑ k ∈ Icc (1 : ℕ) N, (c k : ℂ) *
        (ex (π * (((k : ℤ) - μ : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ))) -
          ex (π * ((-(k : ℤ) - μ : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ)))) := by
    intro i
    unfold sinePoly
    rw [Complex.ofReal_sum, sum_mul, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_mul, ofReal_sin_eq_ex]
    have e1 : ex ((k : ℝ) * π * gridPt N i) * ex (π * μ * (x - gridPt N i)) =
        ex (π * μ * x) * ex (π * (((k : ℤ) - μ : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ))) := by
      rw [← ex_add, ← ex_add]
      unfold gridPt
      congr 1
      push_cast
      ring
    have e2 : ex (-((k : ℝ) * π * gridPt N i)) * ex (π * μ * (x - gridPt N i)) =
        ex (π * μ * x) * ex (π * ((-(k : ℤ) - μ : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ))) := by
      rw [← ex_add, ← ex_add]
      unfold gridPt
      congr 1
      push_cast
      ring
    linear_combination ((c k : ℂ) / (2 * Complex.I)) * e1 - ((c k : ℂ) / (2 * Complex.I)) * e2
  rw [sum_congr rfl fun i _ => hexp i, ← mul_sum, sum_comm]
  have hk : ∀ k ∈ Icc (1 : ℕ) N, ∑ i ∈ range (3 * N), (c k : ℂ) *
      (ex (π * (((k : ℤ) - μ : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ))) -
        ex (π * ((-(k : ℤ) - μ : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ)))) =
      ((3 * N : ℕ) : ℂ) * ((c k : ℂ) *
        ((if (k : ℤ) = μ then 1 else 0) - (if -(k : ℤ) = μ then 1 else 0))) := by
    intro k hk
    have hk1 : 1 ≤ (k : ℤ) := by exact_mod_cast (mem_Icc.mp hk).1
    have hkN : (k : ℤ) ≤ N := by exact_mod_cast (mem_Icc.mp hk).2
    have h1 : |((k : ℤ) - μ)| < ((3 * N : ℕ) : ℤ) := by
      rw [abs_lt]
      push_cast
      constructor <;> linarith
    have h2 : |(-(k : ℤ) - μ)| < ((3 * N : ℕ) : ℤ) := by
      rw [abs_lt]
      push_cast
      constructor <;> linarith
    rw [← mul_sum, sum_sub_distrib, sum_range_ex_grid_of_lt hM h1, sum_range_ex_grid_of_lt hM h2]
    by_cases hkμ : (k : ℤ) = μ
    · have h3 : (k : ℤ) - μ = 0 := by omega
      have h4 : ¬ (-(k : ℤ) - μ = 0) := by omega
      have h5 : ¬ (-(k : ℤ) = μ) := by omega
      rw [ite_eq_left h3, ite_eq_right h4, ite_eq_left hkμ, ite_eq_right h5]
      ring
    · by_cases hkμ' : -(k : ℤ) = μ
      · have h3 : ¬ ((k : ℤ) - μ = 0) := by omega
        have h4 : -(k : ℤ) - μ = 0 := by omega
        rw [ite_eq_right h3, ite_eq_left h4, ite_eq_right hkμ, ite_eq_left hkμ']
        ring
      · have h3 : ¬ ((k : ℤ) - μ = 0) := by omega
        have h4 : ¬ (-(k : ℤ) - μ = 0) := by omega
        rw [ite_eq_right h3, ite_eq_right h4, ite_eq_right hkμ, ite_eq_right hkμ']
        ring
  rw [sum_congr rfl hk, ← mul_sum]
  ring

/-- Picking the term `r = k + r' + N`. -/
theorem sum_range_ite_pos {N k r' : ℕ} (hk : k ≤ N) (hr' : r' < N) (x : ℝ) :
    ∑ r ∈ range (3 * N), (if (k : ℤ) = ((r : ℤ) - r' - N) then
      ex (π * (((r : ℤ) - r' - N : ℤ) : ℝ) * x) else 0) = ex (π * k * x) := by
  rw [sum_eq_single (k + r' + N)]
  · rw [ite_eq_left (by push_cast; ring)]
    congr 1
    push_cast
    ring
  · intro r _ hr
    rw [ite_eq_right]
    omega
  · intro h
    exfalso
    exact h (mem_range.mpr (by omega))

/-- Picking the term `r = r' + N - k`. -/
theorem sum_range_ite_neg {N k r' : ℕ} (hk : k ≤ N) (hr' : r' < N) (x : ℝ) :
    ∑ r ∈ range (3 * N), (if -(k : ℤ) = ((r : ℤ) - r' - N) then
      ex (π * (((r : ℤ) - r' - N : ℤ) : ℝ) * x) else 0) = ex (-(π * k * x)) := by
  rw [sum_eq_single (r' + N - k)]
  · rw [ite_eq_left (by push_cast [Nat.cast_sub (show k ≤ r' + N by omega)]; ring)]
    congr 1
    push_cast [Nat.cast_sub (show k ≤ r' + N by omega)]
    ring
  · intro r _ hr
    rw [ite_eq_right]
    omega
  · intro h
    exfalso
    exact h (mem_range.mpr (by omega))

/-- **Reproduction**: `f(x) = (3N)⁻¹ ∑_{i<3N} f(a_i) V_N(x - a_i)`. -/
theorem sinePoly_reproduce {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (x : ℝ) :
    (sinePoly N c x : ℂ) = ((3 * N : ℕ) : ℂ)⁻¹ *
      ∑ i ∈ range (3 * N), (sinePoly N c (gridPt N i) : ℂ) * sampKernel N (x - gridPt N i) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hM0 : ((3 * N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 3 * N ≠ 0 by omega)
  have h2I : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  set F : ℕ → ℂ := fun i => (sinePoly N c (gridPt N i) : ℂ) with hF
  set G : ℂ := ∑ k ∈ Icc (1 : ℕ) N, (c k : ℂ) * (ex (π * k * x) - ex (-(π * k * x))) with hG
  -- Step A: rearrange the sums
  have hA : ∑ i ∈ range (3 * N), F i * sampKernel N (x - gridPt N i) =
      (N : ℂ)⁻¹ * ∑ r' ∈ range N, ∑ r ∈ range (3 * N), ∑ i ∈ range (3 * N),
        F i * ex (π * (((r : ℤ) - r' - N : ℤ) : ℝ) * (x - gridPt N i)) := by
    have h1 : ∀ i, F i * sampKernel N (x - gridPt N i) = (N : ℂ)⁻¹ * ∑ r ∈ range (3 * N),
        ∑ r' ∈ range N, F i * ex (π * (((r : ℤ) - r' - N : ℤ) : ℝ) * (x - gridPt N i)) := by
      intro i
      unfold sampKernel
      rw [mul_left_comm, mul_sum]
      congr 1
      refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun r' _ => ?_
      push_cast
      ring_nf
    rw [sum_congr rfl fun i _ => h1 i, ← mul_sum]
    congr 1
    conv_lhs => rw [sum_comm]
    conv_lhs => arg 2; ext r; rw [sum_comm]
    conv_lhs => rw [sum_comm]
  -- Step B: each frequency is a projection
  have hB : ∀ r ∈ range (3 * N), ∀ r' ∈ range N,
      ∑ i ∈ range (3 * N), F i * ex (π * (((r : ℤ) - r' - N : ℤ) : ℝ) * (x - gridPt N i)) =
        (3 * N : ℕ) * ex (π * (((r : ℤ) - r' - N : ℤ) : ℝ) * x) / (2 * Complex.I) *
          ∑ k ∈ Icc (1 : ℕ) N, (c k : ℂ) *
            ((if (k : ℤ) = ((r : ℤ) - r' - N) then 1 else 0) -
              (if -(k : ℤ) = ((r : ℤ) - r' - N) then 1 else 0)) := by
    intro r hr r' hr'
    simp only [mem_range] at hr hr'
    exact sum_sinePoly_mul_ex hN c x ((r : ℤ) - r' - N) (by omega) (by omega)
  -- Step C: summing over `r` collapses the indicators
  have hC : ∀ r' ∈ range N, ∑ r ∈ range (3 * N),
      (3 * N : ℕ) * ex (π * (((r : ℤ) - r' - N : ℤ) : ℝ) * x) / (2 * Complex.I) *
        ∑ k ∈ Icc (1 : ℕ) N, (c k : ℂ) *
          ((if (k : ℤ) = ((r : ℤ) - r' - N) then 1 else 0) -
            (if -(k : ℤ) = ((r : ℤ) - r' - N) then 1 else 0)) =
      (3 * N : ℕ) / (2 * Complex.I) * G := by
    intro r' hr'
    have hr'N : r' < N := mem_range.mp hr'
    have key : ∑ r ∈ range (3 * N), ex (π * (((r : ℤ) - r' - N : ℤ) : ℝ) * x) *
        ∑ k ∈ Icc (1 : ℕ) N, (c k : ℂ) *
          ((if (k : ℤ) = ((r : ℤ) - r' - N) then 1 else 0) -
            (if -(k : ℤ) = ((r : ℤ) - r' - N) then 1 else 0)) = G := by
      simp_rw [mul_sum]
      rw [sum_comm, hG]
      refine sum_congr rfl fun k hk => ?_
      have hkN : k ≤ N := (mem_Icc.mp hk).2
      rw [← sum_range_ite_pos hkN hr'N x, ← sum_range_ite_neg hkN hr'N x, ← sum_sub_distrib,
        mul_sum]
      refine sum_congr rfl fun r _ => ?_
      split_ifs <;> ring
    rw [← key, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    ring
  have hsin : (sinePoly N c x : ℂ) = G / (2 * Complex.I) := by
    unfold sinePoly
    rw [Complex.ofReal_sum, hG, sum_div]
    refine sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_mul, ofReal_sin_eq_ex]
    ring_nf
  rw [hA, sum_congr rfl fun r' hr' => sum_congr rfl fun r hr => hB r hr r' hr']
  rw [sum_congr rfl hC, sum_const, card_range, nsmul_eq_mul, hsin]
  field_simp

/-- `V_N(y) = N⁻¹ D_{3N}(y) conj(D_N(y)) e^{-iπNy}`, hence `|V_N| = N⁻¹ |D_{3N}| |D_N|`. -/
theorem norm_sampKernel (N : ℕ) (y : ℝ) :
    ‖sampKernel N y‖ = (N : ℝ)⁻¹ * (‖dirichletSum (3 * N) y‖ * ‖dirichletSum N y‖) := by
  have hfac : sampKernel N y = (N : ℂ)⁻¹ *
      (dirichletSum (3 * N) y * conj (dirichletSum N y) * ex (-(π * N * y))) := by
    unfold sampKernel dirichletSum
    rw [map_sum, sum_mul_sum, sum_mul]
    congr 1
    refine sum_congr rfl fun r _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun r' _ => ?_
    rw [conj_ex, ← ex_add, ← ex_add]
    congr 1
    ring
  rw [hfac, norm_mul, norm_mul, norm_mul, norm_ex, mul_one, Complex.norm_conj, norm_inv,
    Complex.norm_natCast]

/-- **Discrete Parseval**: `∑_{i<3N} |D_K(x - a_i)|² = 3N·K` for `K ≤ 3N`. -/
theorem sum_normSq_dirichletSum {N K : ℕ} (hN : 1 ≤ N) (hK : K ≤ 3 * N) (x : ℝ) :
    ∑ i ∈ range (3 * N), ‖dirichletSum K (x - gridPt N i)‖ ^ 2 = (3 * N : ℕ) * K := by
  have hM : 0 < 3 * N := by omega
  have hc : ∀ i : ℕ, ((‖dirichletSum K (x - gridPt N i)‖ ^ 2 : ℝ) : ℂ) =
      ∑ r ∈ range K, ∑ r' ∈ range K, ex (π * (((r : ℤ) - r' : ℤ) : ℝ) * x) *
        ex (π * (((r' : ℤ) - r : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ))) := by
    intro i
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    unfold dirichletSum
    rw [map_sum, sum_mul_sum]
    refine sum_congr rfl fun r _ => sum_congr rfl fun r' _ => ?_
    rw [conj_ex, ← ex_add, ← ex_add]
    unfold gridPt
    congr 1
    push_cast
    ring
  have hin : ∀ r ∈ range K, ∀ r' ∈ range K,
      ∑ i ∈ range (3 * N), ex (π * (((r : ℤ) - r' : ℤ) : ℝ) * x) *
          ex (π * (((r' : ℤ) - r : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ))) =
        if r = r' then ((3 * N : ℕ) : ℂ) else 0 := by
    intro r hr r' hr'
    have hlt : |((r' : ℤ) - r)| < ((3 * N : ℕ) : ℤ) := by
      simp only [mem_range] at hr hr'
      rw [abs_lt]
      push_cast
      constructor <;> omega
    rw [← mul_sum, sum_range_ex_grid_of_lt hM hlt]
    by_cases h : r = r'
    · subst h
      simp [ex_zero]
    · have h' : ¬ ((r' : ℤ) - r = 0) := by omega
      rw [ite_eq_right h', ite_eq_right h, mul_zero]
  have hsum : ((∑ i ∈ range (3 * N), ‖dirichletSum K (x - gridPt N i)‖ ^ 2 : ℝ) : ℂ) =
      (((3 * N : ℕ) * K : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, sum_congr rfl fun i _ => hc i, sum_comm,
      sum_congr rfl fun r _ => sum_comm,
      sum_congr rfl fun r hr => sum_congr rfl fun r' hr' => hin r hr r' hr',
      sum_congr rfl fun r hr => by rw [sum_ite_eq, ite_eq_left hr], sum_const, card_range,
      nsmul_eq_mul]
    push_cast
    ring
  exact_mod_cast hsum

/-- **Lebesgue constant**: `∑_{i<3N} |V_N(x - a_i)| ≤ (7/4)·3N`. -/
theorem sum_norm_sampKernel_le {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    ∑ i ∈ range (3 * N), ‖sampKernel N (x - gridPt N i)‖ ≤ 7 / 4 * (3 * N : ℕ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpt : ∀ i : ℕ, ‖sampKernel N (x - gridPt N i)‖ ≤ (N : ℝ)⁻¹ *
      (‖dirichletSum (3 * N) (x - gridPt N i)‖ ^ 2 / 4 + ‖dirichletSum N (x - gridPt N i)‖ ^ 2) := by
    intro i
    rw [norm_sampKernel]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith [sq_nonneg (‖dirichletSum (3 * N) (x - gridPt N i)‖ / 2 -
      ‖dirichletSum N (x - gridPt N i)‖)]
  calc ∑ i ∈ range (3 * N), ‖sampKernel N (x - gridPt N i)‖
      ≤ ∑ i ∈ range (3 * N), (N : ℝ)⁻¹ * (‖dirichletSum (3 * N) (x - gridPt N i)‖ ^ 2 / 4 +
          ‖dirichletSum N (x - gridPt N i)‖ ^ 2) := sum_le_sum fun i _ => hpt i
    _ = (N : ℝ)⁻¹ * ((∑ i ∈ range (3 * N), ‖dirichletSum (3 * N) (x - gridPt N i)‖ ^ 2) / 4 +
          ∑ i ∈ range (3 * N), ‖dirichletSum N (x - gridPt N i)‖ ^ 2) := by
        rw [← mul_sum, sum_add_distrib, sum_div]
    _ = 7 / 4 * (3 * N : ℕ) := by
        rw [sum_normSq_dirichletSum hN le_rfl, sum_normSq_dirichletSum hN (by omega)]
        field_simp
        push_cast
        ring

/-- **Sampling for sine polynomials**: for every real `x` there is a grid point `a_i`,
`i < 3N`, with `|f(x)| ≤ (7/4)|f(a_i)|`. -/
theorem sinePoly_le_grid {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (x : ℝ) :
    ∃ i ∈ range (3 * N), |sinePoly N c x| ≤ 7 / 4 * |sinePoly N c (gridPt N i)| := by
  have hne : (range (3 * N)).Nonempty := nonempty_range_iff.mpr (by omega)
  obtain ⟨i₀, hi₀, hmax⟩ := exists_max_image (range (3 * N)) (fun i => |sinePoly N c (gridPt N i)|)
    hne
  refine ⟨i₀, hi₀, ?_⟩
  have hM : (0 : ℝ) < (3 * N : ℕ) := by exact_mod_cast (show 0 < 3 * N by omega)
  have hrep := congrArg norm (sinePoly_reproduce hN c x)
  rw [Complex.norm_real, Real.norm_eq_abs] at hrep
  rw [hrep, norm_mul, norm_inv, Complex.norm_natCast]
  have hb : ‖∑ i ∈ range (3 * N), (sinePoly N c (gridPt N i) : ℂ) * sampKernel N (x - gridPt N i)‖
      ≤ |sinePoly N c (gridPt N i₀)| * (7 / 4 * (3 * N : ℕ)) := by
    calc _ ≤ ∑ i ∈ range (3 * N), ‖(sinePoly N c (gridPt N i) : ℂ) * sampKernel N (x - gridPt N i)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ range (3 * N), |sinePoly N c (gridPt N i₀)| * ‖sampKernel N (x - gridPt N i)‖ := by
          refine sum_le_sum fun i hi => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hmax i hi) (norm_nonneg _)
      _ = |sinePoly N c (gridPt N i₀)| * ∑ i ∈ range (3 * N), ‖sampKernel N (x - gridPt N i)‖ := by
          rw [mul_sum]
      _ ≤ |sinePoly N c (gridPt N i₀)| * (7 / 4 * (3 * N : ℕ)) :=
          mul_le_mul_of_nonneg_left (sum_norm_sampKernel_le hN x) (abs_nonneg _)
  calc ((3 * N : ℕ) : ℝ)⁻¹ * ‖∑ i ∈ range (3 * N),
        (sinePoly N c (gridPt N i) : ℂ) * sampKernel N (x - gridPt N i)‖
      ≤ ((3 * N : ℕ) : ℝ)⁻¹ * (|sinePoly N c (gridPt N i₀)| * (7 / 4 * (3 * N : ℕ))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 7 / 4 * |sinePoly N c (gridPt N i₀)| := by field_simp

/-- Sine polynomials are odd about `x = 1`: `f(2 - x) = -f(x)`. -/
theorem sinePoly_two_sub (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    sinePoly N c (2 - x) = -sinePoly N c x := by
  unfold sinePoly
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  have : (k : ℝ) * π * (2 - x) = ((2 * k : ℕ) : ℝ) * π - (k : ℝ) * π * x := by push_cast; ring
  rw [this, Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  have hpow : ((-1 : ℝ)) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  rw [hpow]
  ring

/-- The band `B_j` is the sine polynomial of degree `2^{j+1}` with `c_k = ρ(kℓ_j) b_k`. -/
theorem band_eq_sinePoly (y : ℝ → ℝ) (j : ℕ) (a : ℝ) :
    band y j a = sinePoly (2 ^ (j + 1)) (fun k => rho ((k : ℝ) * ell j) * sineCoef y k) a := rfl

/-- **Lemma 4.1, (4.5)**: deterministic sampling sets of size `≤ C/ℓ_j` (here `C = 4`). -/
theorem lemma41_sampling :
    ∃ C : ℝ, ∀ j : ℕ, ∃ A : Finset ℝ, (↑A : Set ℝ) ⊆ Set.Icc 0 1 ∧ (A.card : ℝ) ≤ C / ell j ∧
      ∀ y : ℝ → ℝ, ContinuousOn y (Set.Icc 0 1) → ∀ a : ℝ,
        ∃ a' ∈ A, |band y j a| ≤ 2 * |band y j a'| := by
  refine ⟨4, fun j => ?_⟩
  set L : ℕ := 3 * 2 ^ j with hL
  have hLpos : 0 < L := by positivity
  refine ⟨(range (L + 1)).image (fun i : ℕ => (i : ℝ) / L), ?_, ?_, ?_⟩
  · intro t ht
    simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hLr]
    exact_mod_cast (show i ≤ L by omega)
  · calc ((range (L + 1)).image (fun i : ℕ => (i : ℝ) / L)).card ≤ ((range (L + 1)).card : ℝ) := by
          exact_mod_cast card_image_le
      _ = L + 1 := by rw [card_range]; push_cast; ring
      _ ≤ 4 / ell j := by
          rw [div_eq_mul_inv, inv_ell, hL]
          have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
          push_cast
          linarith
  · intro y _ a
    have hN : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    obtain ⟨i, hi, hle⟩ := sinePoly_le_grid hN (fun k => rho ((k : ℝ) * ell j) * sineCoef y k) a
    rw [← band_eq_sinePoly] at hle
    have hgrid : gridPt (2 ^ (j + 1)) i = (i : ℝ) / L := by
      unfold gridPt
      rw [hL]
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity), pow_succ]
      ring
    have hi' : i < 2 * L := by
      rw [mem_range] at hi
      rw [hL]
      calc i < 3 * 2 ^ (j + 1) := hi
        _ = 2 * (3 * 2 ^ j) := by rw [pow_succ]; ring
    by_cases hiL : i ≤ L
    · refine ⟨(i : ℝ) / L, mem_image.mpr ⟨i, mem_range.mpr (by omega), rfl⟩, ?_⟩
      rw [band_eq_sinePoly y j ((i : ℝ) / L), ← hgrid]
      linarith [abs_nonneg (sinePoly (2 ^ (j + 1)) (fun k => rho ((k : ℝ) * ell j) * sineCoef y k)
        (gridPt (2 ^ (j + 1)) i))]
    · refine ⟨((2 * L - i : ℕ) : ℝ) / L, mem_image.mpr ⟨2 * L - i, mem_range.mpr (by omega), rfl⟩,
        ?_⟩
      have hrefl : ((2 * L - i : ℕ) : ℝ) / L = 2 - gridPt (2 ^ (j + 1)) i := by
        rw [hgrid, Nat.cast_sub (by omega)]
        have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
        field_simp
        push_cast
        ring
      rw [hrefl, band_eq_sinePoly y j (2 - gridPt (2 ^ (j + 1)) i), sinePoly_two_sub, abs_neg]
      linarith [abs_nonneg (sinePoly (2 ^ (j + 1)) (fun k => rho ((k : ℝ) * ell j) * sineCoef y k)
        (gridPt (2 ^ (j + 1)) i))]

/-! ### Weak Bernstein inequality (GA2 D4.4; GA3 X7(f)) -/

/-- The weighted exponential sum `∑_{r<K} w_r e^{iπry}`. -/
def weightedSum (K : ℕ) (w : ℕ → ℝ) (y : ℝ) : ℂ := ∑ r ∈ range K, (w r : ℂ) * ex (π * r * y)

/-- **Weighted discrete Parseval**: `∑_{i<3N} |∑_{r<K} w_r e^{iπr(x-a_i)}|² = 3N ∑_{r<K} w_r²`
for `K ≤ 3N`. -/
theorem sum_normSq_weightedSum {N K : ℕ} (hN : 1 ≤ N) (hK : K ≤ 3 * N) (w : ℕ → ℝ) (x : ℝ) :
    ∑ i ∈ range (3 * N), ‖weightedSum K w (x - gridPt N i)‖ ^ 2 =
      (3 * N : ℕ) * ∑ r ∈ range K, w r ^ 2 := by
  have hM : 0 < 3 * N := by omega
  have hc : ∀ i : ℕ, ((‖weightedSum K w (x - gridPt N i)‖ ^ 2 : ℝ) : ℂ) =
      ∑ r ∈ range K, ∑ r' ∈ range K, ((w r * w r' : ℝ) : ℂ) *
        (ex (π * (((r : ℤ) - r' : ℤ) : ℝ) * x) *
          ex (π * (((r' : ℤ) - r : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ)))) := by
    intro i
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    unfold weightedSum
    rw [map_sum, sum_mul_sum]
    refine sum_congr rfl fun r _ => sum_congr rfl fun r' _ => ?_
    rw [map_mul, Complex.conj_ofReal, conj_ex, Complex.ofReal_mul]
    have e : ex (π * r * (x - gridPt N i)) * ex (-(π * r' * (x - gridPt N i))) =
        ex (π * (((r : ℤ) - r' : ℤ) : ℝ) * x) *
          ex (π * (((r' : ℤ) - r : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ))) := by
      rw [← ex_add, ← ex_add]
      unfold gridPt
      congr 1
      push_cast
      ring
    linear_combination ((w r : ℂ) * (w r' : ℂ)) * e
  have hin : ∀ r ∈ range K, ∀ r' ∈ range K,
      ∑ i ∈ range (3 * N), ((w r * w r' : ℝ) : ℂ) * (ex (π * (((r : ℤ) - r' : ℤ) : ℝ) * x) *
          ex (π * (((r' : ℤ) - r : ℤ) : ℝ) * (2 * i / ((3 * N : ℕ) : ℝ)))) =
        if r = r' then ((3 * N : ℕ) : ℂ) * ((w r ^ 2 : ℝ) : ℂ) else 0 := by
    intro r hr r' hr'
    have hlt : |((r' : ℤ) - r)| < ((3 * N : ℕ) : ℤ) := by
      simp only [mem_range] at hr hr'
      rw [abs_lt]
      push_cast
      constructor <;> omega
    rw [← mul_sum, ← mul_sum, sum_range_ex_grid_of_lt hM hlt]
    by_cases h : r = r'
    · subst h
      simp [ex_zero]
      ring
    · have h' : ¬ ((r' : ℤ) - r = 0) := by omega
      rw [ite_eq_right h', ite_eq_right h, mul_zero, mul_zero]
  have hsum : ((∑ i ∈ range (3 * N), ‖weightedSum K w (x - gridPt N i)‖ ^ 2 : ℝ) : ℂ) =
      ((((3 * N : ℕ) : ℝ) * ∑ r ∈ range K, w r ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, sum_congr rfl fun i _ => hc i, sum_comm,
      sum_congr rfl fun r _ => sum_comm,
      sum_congr rfl fun r hr => sum_congr rfl fun r' hr' => hin r hr r' hr',
      sum_congr rfl fun r hr => by rw [sum_ite_eq, ite_eq_left hr]]
    push_cast
    rw [mul_sum]
  exact_mod_cast hsum

theorem hasDerivAt_ex_mul (c y : ℝ) :
    HasDerivAt (fun y => ex (c * y)) (Complex.I * c * ex (c * y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => (((c * y : ℝ) : ℂ) * Complex.I)) ((c : ℂ) * Complex.I) y := by
    have := ((hasDerivAt_id y).const_mul c).ofReal_comp
    simpa using this.mul_const Complex.I
  have h2 := h1.cexp
  unfold ex
  refine h2.congr_deriv ?_
  ring

/-- The derivative `V_N'(y) = N⁻¹ ∑_{r<3N} ∑_{r'<N} iπ(r-r'-N) e^{iπ(r-r'-N)y}`. -/
def sampKernelDeriv (N : ℕ) (y : ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ r ∈ range (3 * N), ∑ r' ∈ range N,
    (Complex.I * ((π * ((r : ℝ) - r' - N) : ℝ) : ℂ)) * ex (π * ((r : ℝ) - r' - N) * y)

theorem hasDerivAt_sampKernel (N : ℕ) (y : ℝ) :
    HasDerivAt (sampKernel N) (sampKernelDeriv N y) y := by
  unfold sampKernel sampKernelDeriv
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun r _ => HasDerivAt.fun_sum fun r' _ => ?_)
  exact hasDerivAt_ex_mul (π * ((r : ℝ) - r' - N)) y

/-- `|V_N'| ≤ N⁻¹ π (|A| |D_N| + |D_{3N}| |B|)` with `A = ∑_{r<3N} r e^{iπr·}` and
`B = ∑_{r'<N} (r'+N) e^{iπr'·}`. -/
theorem norm_sampKernelDeriv_le (N : ℕ) (y : ℝ) :
    ‖sampKernelDeriv N y‖ ≤ (N : ℝ)⁻¹ * π *
      (‖weightedSum (3 * N) (fun r => (r : ℝ)) y‖ * ‖dirichletSum N y‖ +
        ‖dirichletSum (3 * N) y‖ * ‖weightedSum N (fun r' => (r' : ℝ) + N) y‖) := by
  have hexp : (weightedSum (3 * N) (fun r => (r : ℝ)) y * conj (dirichletSum N y) -
      dirichletSum (3 * N) y * conj (weightedSum N (fun r' => (r' : ℝ) + N) y)) *
        ex (-(π * N * y)) = ∑ r ∈ range (3 * N), ∑ r' ∈ range N,
          (((r : ℝ) - r' - N : ℝ) : ℂ) * ex (π * ((r : ℝ) - r' - N) * y) := by
    unfold weightedSum dirichletSum
    rw [map_sum, map_sum, sum_mul_sum, sum_mul_sum, ← sum_sub_distrib, sum_mul]
    refine sum_congr rfl fun r _ => ?_
    rw [← sum_sub_distrib, sum_mul]
    refine sum_congr rfl fun r' _ => ?_
    rw [map_mul, Complex.conj_ofReal, conj_ex]
    have e1 : ex (π * r * y) * ex (-(π * r' * y)) * ex (-(π * N * y)) =
        ex (π * ((r : ℝ) - r' - N) * y) := by
      rw [← ex_add, ← ex_add]
      congr 1
      ring
    push_cast
    linear_combination ((r : ℂ) - r' - N) * e1
  have hfac : sampKernelDeriv N y = (N : ℂ)⁻¹ * (Complex.I * π) *
      ((weightedSum (3 * N) (fun r => (r : ℝ)) y * conj (dirichletSum N y) -
        dirichletSum (3 * N) y * conj (weightedSum N (fun r' => (r' : ℝ) + N) y)) *
          ex (-(π * N * y))) := by
    unfold sampKernelDeriv
    rw [mul_assoc, hexp]
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun r' _ => ?_
    push_cast
    ring
  rw [hfac, norm_mul, norm_mul, norm_mul, norm_mul, norm_ex, mul_one, Complex.norm_I, one_mul,
    norm_inv, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖weightedSum (3 * N) (fun r => (r : ℝ)) y * conj (dirichletSum N y) -
        dirichletSum (3 * N) y * conj (weightedSum N (fun r' => (r' : ℝ) + N) y)‖
      ≤ ‖weightedSum (3 * N) (fun r => (r : ℝ)) y * conj (dirichletSum N y)‖ +
        ‖dirichletSum (3 * N) y * conj (weightedSum N (fun r' => (r' : ℝ) + N) y)‖ :=
        norm_sub_le _ _
    _ = _ := by rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]

theorem sum_range_sq_le (K : ℕ) : ∑ r ∈ range K, ((r : ℝ)) ^ 2 ≤ (K : ℝ) ^ 3 := by
  calc ∑ r ∈ range K, ((r : ℝ)) ^ 2 ≤ ∑ _r ∈ range K, (K : ℝ) ^ 2 := by
        refine sum_le_sum fun r hr => ?_
        have : (r : ℝ) ≤ K := by exact_mod_cast (mem_range.mp hr).le
        exact pow_le_pow_left₀ (by positivity) this 2
    _ = (K : ℝ) ^ 3 := by rw [sum_const, card_range, nsmul_eq_mul]; ring

theorem sum_range_add_sq_le (N : ℕ) : ∑ r ∈ range N, ((r : ℝ) + N) ^ 2 ≤ 4 * (N : ℝ) ^ 3 := by
  calc ∑ r ∈ range N, ((r : ℝ) + N) ^ 2 ≤ ∑ _r ∈ range N, (2 * (N : ℝ)) ^ 2 := by
        refine sum_le_sum fun r hr => ?_
        have : (r : ℝ) ≤ N := by exact_mod_cast (mem_range.mp hr).le
        exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    _ = 4 * (N : ℝ) ^ 3 := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- `∑_{i<3N} |V_N'(x - a_i)| ≤ (35π/2) N · 3N`. -/
theorem sum_norm_sampKernelDeriv_le {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    ∑ i ∈ range (3 * N), ‖sampKernelDeriv N (x - gridPt N i)‖ ≤
      35 * π / 2 * N * (3 * N : ℕ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set A := fun i : ℕ => ‖weightedSum (3 * N) (fun r => (r : ℝ)) (x - gridPt N i)‖ with hA
  set D1 := fun i : ℕ => ‖dirichletSum N (x - gridPt N i)‖ with hD1
  set D3 := fun i : ℕ => ‖dirichletSum (3 * N) (x - gridPt N i)‖ with hD3
  set B := fun i : ℕ => ‖weightedSum N (fun r' => (r' : ℝ) + N) (x - gridPt N i)‖ with hB
  have hpt : ∀ i : ℕ, ‖sampKernelDeriv N (x - gridPt N i)‖ ≤ (N : ℝ)⁻¹ * π *
      ((A i ^ 2 / N + N * D1 i ^ 2) / 2 + (N * D3 i ^ 2 + B i ^ 2 / N) / 2) := by
    intro i
    refine (norm_sampKernelDeriv_le N _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h1 : A i * D1 i ≤ (A i ^ 2 / N + N * D1 i ^ 2) / 2 := by
      have := sq_nonneg (A i - N * D1 i)
      rw [div_add' _ _ _ hNpos.ne', div_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : D3 i * B i ≤ (N * D3 i ^ 2 + B i ^ 2 / N) / 2 := by
      have := sq_nonneg (N * D3 i - B i)
      rw [add_div' _ _ _ hNpos.ne', div_div, le_div_iff₀ (by positivity)]
      nlinarith
    exact add_le_add h1 h2
  have sA : ∑ i ∈ range (3 * N), A i ^ 2 ≤ (3 * N : ℕ) * ((3 * N : ℕ) : ℝ) ^ 3 := by
    rw [hA]
    simp only
    rw [sum_normSq_weightedSum hN le_rfl]
    exact mul_le_mul_of_nonneg_left (sum_range_sq_le _) (by positivity)
  have sD1 : ∑ i ∈ range (3 * N), D1 i ^ 2 = (3 * N : ℕ) * N := by
    rw [hD1]; exact sum_normSq_dirichletSum hN (by omega) x
  have sD3 : ∑ i ∈ range (3 * N), D3 i ^ 2 = (3 * N : ℕ) * (3 * N : ℕ) := by
    rw [hD3]; exact sum_normSq_dirichletSum hN le_rfl x
  have sB : ∑ i ∈ range (3 * N), B i ^ 2 ≤ (3 * N : ℕ) * (4 * (N : ℝ) ^ 3) := by
    rw [hB]
    simp only
    rw [sum_normSq_weightedSum hN (by omega)]
    exact mul_le_mul_of_nonneg_left (sum_range_add_sq_le N) (by positivity)
  calc ∑ i ∈ range (3 * N), ‖sampKernelDeriv N (x - gridPt N i)‖
      ≤ ∑ i ∈ range (3 * N), (N : ℝ)⁻¹ * π *
          ((A i ^ 2 / N + N * D1 i ^ 2) / 2 + (N * D3 i ^ 2 + B i ^ 2 / N) / 2) :=
        sum_le_sum fun i _ => hpt i
    _ = (N : ℝ)⁻¹ * π * ((∑ i ∈ range (3 * N), A i ^ 2) / N / 2 +
          N * (∑ i ∈ range (3 * N), D1 i ^ 2) / 2 + N * (∑ i ∈ range (3 * N), D3 i ^ 2) / 2 +
          (∑ i ∈ range (3 * N), B i ^ 2) / N / 2) := by
        rw [← mul_sum]
        congr 1
        rw [sum_div, sum_div, mul_sum, sum_div, mul_sum, sum_div, sum_div, sum_div,
          ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        ring
    _ ≤ (N : ℝ)⁻¹ * π * (((3 * N : ℕ) * ((3 * N : ℕ) : ℝ) ^ 3) / N / 2 +
          N * ((3 * N : ℕ) * N) / 2 + N * ((3 * N : ℕ) * (3 * N : ℕ)) / 2 +
          ((3 * N : ℕ) * (4 * (N : ℝ) ^ 3)) / N / 2) := by
        rw [sD1, sD3]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1 : (∑ i ∈ range (3 * N), A i ^ 2) / N / 2 ≤
            ((3 * N : ℕ) * ((3 * N : ℕ) : ℝ) ^ 3) / N / 2 := by
          gcongr
        have h2 : (∑ i ∈ range (3 * N), B i ^ 2) / N / 2 ≤
            ((3 * N : ℕ) * (4 * (N : ℝ) ^ 3)) / N / 2 := by
          gcongr
        linarith
    _ = 35 * π / 2 * N * (3 * N : ℕ) + 0 := by
        push_cast
        field_simp
        ring
    _ ≤ 35 * π / 2 * N * (3 * N : ℕ) := by linarith

theorem hasDerivAt_sinePoly (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (sinePoly N c)
      (∑ k ∈ Icc (1 : ℕ) N, c k * ((k : ℝ) * π) * Real.cos (((k : ℝ) * π) * x)) x := by
  unfold sinePoly
  exact hasDerivAt_sum_sin (Icc (1 : ℕ) N) c (fun k => (k : ℝ) * π) x

/-- Differentiated reproduction: `f'(x) = (3N)⁻¹ ∑_i f(a_i) V_N'(x - a_i)`. -/
theorem deriv_sinePoly_eq {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (x : ℝ) :
    ((deriv (sinePoly N c) x : ℝ) : ℂ) = ((3 * N : ℕ) : ℂ)⁻¹ *
      ∑ i ∈ range (3 * N), (sinePoly N c (gridPt N i) : ℂ) * sampKernelDeriv N (x - gridPt N i) := by
  have hf := hasDerivAt_sinePoly N c x
  have h1 : HasDerivAt (fun x => (sinePoly N c x : ℂ)) ((deriv (sinePoly N c) x : ℝ) : ℂ) x := by
    rw [hf.deriv]
    exact hf.ofReal_comp
  have h2 : HasDerivAt (fun x => ((3 * N : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (3 * N),
      (sinePoly N c (gridPt N i) : ℂ) * sampKernel N (x - gridPt N i))
      (((3 * N : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (3 * N),
        (sinePoly N c (gridPt N i) : ℂ) * sampKernelDeriv N (x - gridPt N i)) x := by
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun i _ => ?_)
    refine HasDerivAt.const_mul _ ?_
    have := (hasDerivAt_sampKernel N (x - gridPt N i)).scomp x
      ((hasDerivAt_id' x).sub_const (gridPt N i))
    simpa [Function.comp_def] using this
  have heq : (fun x => (sinePoly N c x : ℂ)) = fun x => ((3 * N : ℕ) : ℂ)⁻¹ *
      ∑ i ∈ range (3 * N), (sinePoly N c (gridPt N i) : ℂ) * sampKernel N (x - gridPt N i) :=
    funext fun x => sinePoly_reproduce hN c x
  rw [heq] at h1
  exact h1.unique h2

/-- **Weak Bernstein inequality** (GA2 D4.4): if `|f| ≤ M` on `ℝ` for a sine polynomial of degree
`N`, then `|f'| ≤ (35π/2) N M`. -/
theorem abs_deriv_sinePoly_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {M : ℝ}
    (hM : ∀ x, |sinePoly N c x| ≤ M) (x : ℝ) :
    |deriv (sinePoly N c) x| ≤ 35 * π / 2 * N * M := by
  have hMpos : (0 : ℝ) < (3 * N : ℕ) := by exact_mod_cast (show 0 < 3 * N by omega)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have h := congrArg norm (deriv_sinePoly_eq hN c x)
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  rw [h, norm_mul, norm_inv, Complex.norm_natCast]
  have hb : ‖∑ i ∈ range (3 * N), (sinePoly N c (gridPt N i) : ℂ) *
      sampKernelDeriv N (x - gridPt N i)‖ ≤ M * (35 * π / 2 * N * (3 * N : ℕ)) := by
    calc _ ≤ ∑ i ∈ range (3 * N), ‖(sinePoly N c (gridPt N i) : ℂ) *
          sampKernelDeriv N (x - gridPt N i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range (3 * N), M * ‖sampKernelDeriv N (x - gridPt N i)‖ := by
          refine sum_le_sum fun i _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
      _ = M * ∑ i ∈ range (3 * N), ‖sampKernelDeriv N (x - gridPt N i)‖ := by rw [mul_sum]
      _ ≤ M * (35 * π / 2 * N * (3 * N : ℕ)) :=
          mul_le_mul_of_nonneg_left (sum_norm_sampKernelDeriv_le hN x) hM0
  calc ((3 * N : ℕ) : ℝ)⁻¹ * ‖∑ i ∈ range (3 * N), (sinePoly N c (gridPt N i) : ℂ) *
        sampKernelDeriv N (x - gridPt N i)‖
      ≤ ((3 * N : ℕ) : ℝ)⁻¹ * (M * (35 * π / 2 * N * (3 * N : ℕ))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 35 * π / 2 * N * M := by field_simp

/-- Lipschitz form of the weak Bernstein inequality. -/
theorem sinePoly_lipschitz {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {M : ℝ}
    (hM : ∀ x, |sinePoly N c x| ≤ M) (s t : ℝ) :
    |sinePoly N c s - sinePoly N c t| ≤ 35 * π / 2 * N * M * |s - t| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (f := sinePoly N c)
    (C := 35 * π / 2 * N * M) (x := t) (y := s)
    (fun z _ => (hasDerivAt_sinePoly N c z).differentiableAt)
    (fun z _ => by rw [Real.norm_eq_abs]; exact abs_deriv_sinePoly_le hN c hM z)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this

/-- **Band regularity** (GA3 X7(f), used for (6.5)): if `|B_j| ≤ M` on `ℝ`, then
`|B_j(s) - B_j(t)| ≤ 35π M |s - t| / ℓ_j`. -/
theorem band_lipschitz (y : ℝ → ℝ) (j : ℕ) {M : ℝ} (hM : ∀ a, |band y j a| ≤ M) (s t : ℝ) :
    |band y j s - band y j t| ≤ 35 * π * M * |s - t| / ell j := by
  have hN : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have h := sinePoly_lipschitz hN (fun k => rho ((k : ℝ) * ell j) * sineCoef y k) (M := M)
    (fun x => by rw [← band_eq_sinePoly]; exact hM x) s t
  rw [← band_eq_sinePoly, ← band_eq_sinePoly] at h
  have he : (35 * π / 2 * ((2 ^ (j + 1) : ℕ) : ℝ) * M * |s - t|) = 35 * π * M * |s - t| / ell j := by
    rw [div_eq_mul_inv _ (ell j), inv_ell]
    push_cast
    ring
  rwa [he] at h

/-- `|B_j(s) - B_j(t)| ≤ 35π M min(1, |s - t|/ℓ_j)` when `|B_j| ≤ M` on `ℝ`. -/
theorem band_holder (y : ℝ → ℝ) (j : ℕ) {M : ℝ} (hM : ∀ a, |band y j a| ≤ M) (s t : ℝ) :
    |band y j s - band y j t| ≤ 35 * π * M * min 1 (|s - t| / ell j) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  rcases le_total 1 (|s - t| / ell j) with h | h
  · rw [min_eq_left h, mul_one]
    calc |band y j s - band y j t| ≤ |band y j s| + |band y j t| := abs_sub _ _
      _ ≤ M + M := add_le_add (hM s) (hM t)
      _ ≤ 35 * π * M := by nlinarith [Real.two_le_pi]
  · rw [min_eq_right h]
    have := band_lipschitz y j hM s t
    calc |band y j s - band y j t| ≤ 35 * π * M * |s - t| / ell j := this
      _ = 35 * π * M * (|s - t| / ell j) := by ring

/-- **Lemma 4.1 (c), band increments** (blueprint form, `C_B = 35`): if `|B_j| ≤ M` on `ℝ`, then
`|B_j(t) - B_j(s)| ≤ M min{2, 35π|t - s|/ℓ_j}`. -/
theorem band_increment (y : ℝ → ℝ) (j : ℕ) {M : ℝ} (hM : ∀ a, |band y j a| ≤ M) (s t : ℝ) :
    |band y j t - band y j s| ≤ M * min 2 (35 * π * |t - s| / ell j) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  rcases le_total 2 (35 * π * |t - s| / ell j) with h | h
  · rw [min_eq_left h]
    calc |band y j t - band y j s| ≤ |band y j t| + |band y j s| := abs_sub _ _
      _ ≤ M + M := add_le_add (hM t) (hM s)
      _ = M * 2 := by ring
  · rw [min_eq_right h]
    calc |band y j t - band y j s| ≤ 35 * π * M * |t - s| / ell j := band_lipschitz y j hM t s
      _ = M * (35 * π * |t - s| / ell j) := by ring

/-- **Weak Bernstein inequality** (blueprint form of GA2 D4.4, `C_B = 35`): for
`T(θ) = ∑_{k=1}^{2n} c_k sin(kθ)` with `|T| ≤ M` on `ℝ`, `|T'| ≤ 35 n M`. -/
theorem weak_bernstein {n : ℕ} (hn : 1 ≤ n) (c : ℕ → ℝ) {M : ℝ}
    (hM : ∀ θ : ℝ, |∑ k ∈ Icc (1 : ℕ) (2 * n), c k * Real.sin ((k : ℝ) * θ)| ≤ M) (θ : ℝ) :
    |deriv (fun θ : ℝ => ∑ k ∈ Icc (1 : ℕ) (2 * n), c k * Real.sin ((k : ℝ) * θ)) θ| ≤
      35 * n * M := by
  have hN : 1 ≤ 2 * n := by omega
  have hT : (fun θ : ℝ => ∑ k ∈ Icc (1 : ℕ) (2 * n), c k * Real.sin ((k : ℝ) * θ)) =
      fun θ => sinePoly (2 * n) c (θ / π) := by
    funext θ
    unfold sinePoly
    refine sum_congr rfl fun k _ => ?_
    congr 2
    field_simp
  have hf : ∀ x, |sinePoly (2 * n) c x| ≤ M := by
    intro x
    have h := hM (π * x)
    have e : ∑ k ∈ Icc (1 : ℕ) (2 * n), c k * Real.sin ((k : ℝ) * (π * x)) = sinePoly (2 * n) c x := by
      unfold sinePoly
      refine sum_congr rfl fun k _ => ?_
      congr 2
      ring
    rwa [e] at h
  have hd : HasDerivAt (fun θ => sinePoly (2 * n) c (θ / π))
      (deriv (sinePoly (2 * n) c) (θ / π) * (1 / π)) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => θ / π) (1 / π) θ := (hasDerivAt_id θ).div_const π
    exact (hasDerivAt_sinePoly (2 * n) c (θ / π)).differentiableAt.hasDerivAt.comp θ h1
  rw [hT, hd.deriv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  have hb := abs_deriv_sinePoly_le hN c hf (θ / π)
  calc |deriv (sinePoly (2 * n) c) (θ / π)| * (1 / π) ≤ 35 * π / 2 * ((2 * n : ℕ) : ℝ) * M * (1 / π) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = 35 * n * M := by push_cast; field_simp

end SmallGammaGeodesics
