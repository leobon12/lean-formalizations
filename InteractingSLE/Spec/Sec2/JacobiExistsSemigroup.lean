/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Jacobi semigroup on polynomials

Packet PROVE-YW-JACOBI (existence of the two-sided Jacobi diffusion, Specification p. 22,
`source/spec/p001-048.md` L498–L506). The Jacobi generator

  `L p = (κ/4) X (1 - X) p'' + ½ (a (1 - X) - b X) p'`   (`genL`)

maps the polynomials of degree `< n` (`Polynomial.degreeLT ℝ n`) into themselves. On each of these
finite-dimensional spaces the semigroup `exp (t L)` is the matrix exponential; this file packages it
as a map `semi κ a b t : ℝ[X] → ℝ[X]` and proves its basic properties from one uniqueness statement:

* a *flow* (`IsFlow`) is a curve `y : ℝ → ℝ[X]` of bounded degree whose coefficients satisfy
  `d/dt (y t).coeff k = (L (y t)).coeff k`; two flows with the same value at `0` coincide
  (`IsFlow.eq`, the uniqueness theorem for linear ODEs on `Fin n → ℝ`);
* `t ↦ semi t p` is the flow through `p` (`isFlow_semi`), built from `exp (t • A)` with `A` the
  matrix of `L` on `degreeLT ℝ (natDegree p + 1)`.

Consequences: linearity (`semi_add`, `semi_smul`), `semi t (C c) = C c`, the semigroup law
`semi s (semi t p) = semi (s + t) p`, the commutation `semi t (L p) = L (semi t p)`, degree bounds,
and the time derivative of `t ↦ (semi t p).eval x` (`hasDerivAt_eval_semi`).
-/

set_option autoImplicit false

noncomputable section

open Polynomial Filter Topology

namespace InteractingSLE

namespace Sec2

namespace JacobiExists

variable (κ a b : ℝ)

/-! ### The generator on polynomials -/

/-- The Jacobi generator `L p = (κ/4) X (1 - X) p'' + ½ (a (1 - X) - b X) p'` on `ℝ[X]`. -/
def genL : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun p := C (κ / 4) * (X * (1 - X)) * derivative (derivative p) +
    C (1 / 2) * (C a * (1 - X) - C b * X) * derivative p
  map_add' p q := by simp only [derivative_add]; ring
  map_smul' c p := by
    simp only [RingHom.id_apply, smul_eq_C_mul, derivative_C_mul]
    ring

theorem genL_apply (p : ℝ[X]) :
    genL κ a b p = C (κ / 4) * (X * (1 - X)) * derivative (derivative p) +
      C (1 / 2) * (C a * (1 - X) - C b * X) * derivative p := rfl

theorem eval_genL (p : ℝ[X]) (x : ℝ) :
    (genL κ a b p).eval x = κ / 4 * (x * (1 - x)) * (derivative (derivative p)).eval x +
      (a * (1 - x) - b * x) / 2 * (derivative p).eval x := by
  simp only [genL_apply, eval_add, eval_mul, eval_C, eval_sub, eval_X, eval_one]
  ring

@[simp] theorem genL_C (c : ℝ) : genL κ a b (C c) = 0 := by
  simp [genL_apply]

theorem genL_X_pow (n : ℕ) :
    genL κ a b (X ^ n) = C (κ / 4 * (n * ((n : ℝ) - 1)) + n * a / 2) * X ^ (n - 1) +
      C (-(κ / 4 * (n * ((n : ℝ) - 1)) + n * (a + b) / 2)) * X ^ n := by
  apply Polynomial.funext
  intro x
  rw [eval_genL]
  rcases n with _ | _ | n
  · simp
  · simp
    ring
  · simp only [derivative_X_pow, derivative_C_mul, eval_mul, eval_C, eval_pow, eval_X, eval_add]
    have e1 : n + 2 - 1 = n + 1 := by omega
    have e2 : n + 1 - 1 = n := by omega
    simp only [e1, e2, Nat.cast_add, Nat.cast_one]
    ring

/-- `L` preserves `degreeLT ℝ n`. -/
theorem genL_mem_degreeLT {n : ℕ} {p : ℝ[X]} (hp : p ∈ degreeLT ℝ n) :
    genL κ a b p ∈ degreeLT ℝ n := by
  classical
  rw [degreeLT_eq_span_X_pow] at hp ⊢
  induction hp using Submodule.span_induction with
  | mem q hq =>
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    rw [genL_X_pow]
    refine Submodule.add_mem _ ?_ ?_
    · rw [← smul_eq_C_mul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      exact ⟨k - 1, by omega, rfl⟩
    · rw [← smul_eq_C_mul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      exact ⟨k, hk, rfl⟩
  | zero => simp
  | add p q _ _ hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | smul c p _ hp => rw [map_smul]; exact Submodule.smul_mem _ _ hp

/-! ### Coefficient vectors -/

theorem mem_degreeLT_natDegree_succ (p : ℝ[X]) : p ∈ degreeLT ℝ (p.natDegree + 1) := by
  rw [mem_degreeLT]
  exact (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_self _)

theorem coeff_degreeLTEquiv_symm {n : ℕ} (v : Fin n → ℝ) (k : ℕ) :
    (((degreeLTEquiv ℝ n).symm v : degreeLT ℝ n) : ℝ[X]).coeff k =
      if h : k < n then v ⟨k, h⟩ else 0 := by
  set q := (degreeLTEquiv ℝ n).symm v
  split_ifs with h
  · have := congrFun ((degreeLTEquiv ℝ n).apply_symm_apply v) ⟨k, h⟩
    exact this
  · have hq := mem_degreeLT.1 q.2
    exact coeff_eq_zero_of_degree_lt (hq.trans_le (by exact_mod_cast not_lt.1 h))

theorem coeff_eq_zero_of_mem_degreeLT {n : ℕ} {p : ℝ[X]} (hp : p ∈ degreeLT ℝ n) {k : ℕ}
    (hk : n ≤ k) : p.coeff k = 0 :=
  coeff_eq_zero_of_degree_lt ((mem_degreeLT.1 hp).trans_le (by exact_mod_cast hk))

/-- A polynomial of degree `< n` is the sum of its first `n` monomials. -/
theorem eq_sum_of_mem_degreeLT {n : ℕ} {p : ℝ[X]} (hp : p ∈ degreeLT ℝ n) :
    p = ∑ i ∈ Finset.range n, C (p.coeff i) * X ^ i := by
  rcases eq_or_ne p 0 with rfl | h0
  · simp
  have hd : p.natDegree < n := by
    have := mem_degreeLT.1 hp
    rw [degree_eq_natDegree h0] at this
    exact_mod_cast this
  conv_lhs => rw [as_sum_range' p n hd]
  simp only [C_mul_X_pow_eq_monomial]

/-- The matrix of `L` on `degreeLT ℝ n`, as a continuous linear map on coefficient vectors. -/
def genMat (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    ((degreeLTEquiv ℝ n).toLinearMap ∘ₗ
      ((genL κ a b).restrict fun _ hp => genL_mem_degreeLT κ a b hp) ∘ₗ
        (degreeLTEquiv ℝ n).symm.toLinearMap)

theorem genMat_apply_coeff {n : ℕ} {p : ℝ[X]} (hp : p ∈ degreeLT ℝ n) (i : Fin n) :
    genMat κ a b n (degreeLTEquiv ℝ n ⟨p, hp⟩) i = (genL κ a b p).coeff i := by
  simp only [genMat, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]
  rfl

/-! ### Flows -/

/-- A *flow* of `L`: a curve of bounded degree whose coefficients solve `y' = L y`. -/
def IsFlow (y : ℝ → ℝ[X]) : Prop :=
  ∃ n : ℕ, (∀ t, y t ∈ degreeLT ℝ n) ∧
    ∀ t (k : ℕ), HasDerivAt (fun s => (y s).coeff k) ((genL κ a b (y t)).coeff k) t

variable {κ a b}

theorem IsFlow.mono {y : ℝ → ℝ[X]} {n m : ℕ} (hn : ∀ t, y t ∈ degreeLT ℝ n) (hnm : n ≤ m) :
    ∀ t, y t ∈ degreeLT ℝ m := fun t => degreeLT_mono hnm (hn t)

theorem IsFlow.sub {y z : ℝ → ℝ[X]} (hy : IsFlow κ a b y) (hz : IsFlow κ a b z) :
    IsFlow κ a b (fun t => y t - z t) := by
  obtain ⟨n, hn, hy⟩ := hy
  obtain ⟨m, hm, hz⟩ := hz
  refine ⟨max n m, fun t => Submodule.sub_mem _ (degreeLT_mono (le_max_left n m) (hn t))
    (degreeLT_mono (le_max_right n m) (hm t)), fun t k => ?_⟩
  simp only [coeff_sub, map_sub]
  exact (hy t k).sub (hz t k)

theorem IsFlow.add {y z : ℝ → ℝ[X]} (hy : IsFlow κ a b y) (hz : IsFlow κ a b z) :
    IsFlow κ a b (fun t => y t + z t) := by
  obtain ⟨n, hn, hy⟩ := hy
  obtain ⟨m, hm, hz⟩ := hz
  refine ⟨max n m, fun t => Submodule.add_mem _ (degreeLT_mono (le_max_left n m) (hn t))
    (degreeLT_mono (le_max_right n m) (hm t)), fun t k => ?_⟩
  simp only [coeff_add, map_add]
  exact (hy t k).add (hz t k)

theorem IsFlow.smul {y : ℝ → ℝ[X]} (hy : IsFlow κ a b y) (c : ℝ) :
    IsFlow κ a b (fun t => c • y t) := by
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨n, fun t => Submodule.smul_mem _ c (hn t), fun t k => ?_⟩
  simp only [coeff_smul, map_smul, smul_eq_mul]
  exact (hy t k).const_mul c

theorem isFlow_const {p : ℝ[X]} (hp : genL κ a b p = 0) : IsFlow κ a b (fun _ => p) :=
  ⟨p.natDegree + 1, fun _ => mem_degreeLT_natDegree_succ p, fun t k => by
    rw [hp, coeff_zero]; exact hasDerivAt_const _ _⟩

theorem IsFlow.comp_add {y : ℝ → ℝ[X]} (hy : IsFlow κ a b y) (c : ℝ) :
    IsFlow κ a b (fun t => y (t + c)) := by
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨n, fun t => hn _, fun t k => ?_⟩
  have := (hy (t + c) k).comp t ((hasDerivAt_id t).add_const c)
  simpa [Function.comp_def] using this

/-- **Uniqueness of flows.** -/
theorem IsFlow.eq {y z : ℝ → ℝ[X]} (hy : IsFlow κ a b y) (hz : IsFlow κ a b z)
    (h0 : y 0 = z 0) : y = z := by
  obtain ⟨n, hn, hw⟩ := hy.sub hz
  set v : ℝ → Fin n → ℝ := fun t => degreeLTEquiv ℝ n ⟨y t - z t, hn t⟩ with hv
  have hder : ∀ t, HasDerivAt v (genMat κ a b n (v t)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    rw [hv, genMat_apply_coeff]
    exact hw t i
  have hv0 : v = fun _ => 0 := by
    refine ODE_solution_unique_univ (v := fun _ x => genMat κ a b n x) (s := fun _ => Set.univ)
      (K := ‖genMat κ a b n‖₊) (t₀ := 0) (fun _ => (genMat κ a b n).lipschitzWith.lipschitzOnWith)
      (fun t => ⟨hder t, Set.mem_univ _⟩)
      (fun t => ⟨by simpa using hasDerivAt_const t (0 : Fin n → ℝ), Set.mem_univ _⟩) ?_
    simp only [hv, h0, sub_self]
    exact (degreeLTEquiv ℝ n).map_zero
  funext t
  have h1 := congrFun hv0 t
  simp only [hv] at h1
  have h2 : (⟨y t - z t, hn t⟩ : degreeLT ℝ n) = 0 :=
    (degreeLTEquiv ℝ n).injective (by rw [h1, map_zero])
  exact sub_eq_zero.1 (congrArg Subtype.val h2)

/-! ### The semigroup -/

variable (κ a b)

/-- The coefficient vector of `p` in `degreeLT ℝ (natDegree p + 1)`. -/
def vecOf (p : ℝ[X]) : Fin (p.natDegree + 1) → ℝ :=
  degreeLTEquiv ℝ (p.natDegree + 1) ⟨p, mem_degreeLT_natDegree_succ p⟩

/-- **The Jacobi semigroup** `exp (t L)` on polynomials. -/
def semi (t : ℝ) (p : ℝ[X]) : ℝ[X] :=
  ((degreeLTEquiv ℝ (p.natDegree + 1)).symm
    (NormedSpace.exp (t • genMat κ a b (p.natDegree + 1)) (vecOf p)) : ℝ[X])

theorem semi_mem_degreeLT_succ (t : ℝ) (p : ℝ[X]) :
    semi κ a b t p ∈ degreeLT ℝ (p.natDegree + 1) :=
  ((degreeLTEquiv ℝ (p.natDegree + 1)).symm _).2

theorem isFlow_semi (p : ℝ[X]) : IsFlow κ a b (fun t => semi κ a b t p) := by
  set N := p.natDegree + 1
  set A := genMat κ a b N
  refine ⟨N, fun t => semi_mem_degreeLT_succ κ a b t p, fun t k => ?_⟩
  have hE : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) (vecOf p))
      ((A * NormedSpace.exp (t • A)) (vecOf p)) t := by
    have := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t).clm_apply (hasDerivAt_const t (vecOf p))
    simpa using this
  by_cases hk : k < N
  · have h1 : ∀ s, (semi κ a b s p).coeff k = NormedSpace.exp (s • A) (vecOf p) ⟨k, hk⟩ := by
      intro s
      simp only [semi, coeff_degreeLTEquiv_symm]
      rw [dite_eq_left_of_eq_true (eq_true hk)]
    simp only [h1]
    refine ((hasDerivAt_pi.1 hE) ⟨k, hk⟩).congr_deriv ?_
    show _ = (genL κ a b (semi κ a b t p)).coeff ((⟨k, hk⟩ : Fin N) : ℕ)
    rw [← genMat_apply_coeff κ a b (semi_mem_degreeLT_succ κ a b t p) ⟨k, hk⟩]
    have e : degreeLTEquiv ℝ N ⟨semi κ a b t p, semi_mem_degreeLT_succ κ a b t p⟩ =
        NormedSpace.exp (t • A) (vecOf p) := by
      have : (⟨semi κ a b t p, semi_mem_degreeLT_succ κ a b t p⟩ : degreeLT ℝ N) =
          (degreeLTEquiv ℝ N).symm (NormedSpace.exp (t • A) (vecOf p)) := rfl
      rw [this, LinearEquiv.apply_symm_apply]
    rw [e]
    rfl
  · have h1 : ∀ s, (semi κ a b s p).coeff k = 0 := fun s =>
      coeff_eq_zero_of_mem_degreeLT (semi_mem_degreeLT_succ κ a b s p) (not_lt.1 hk)
    simp only [h1]
    rw [coeff_eq_zero_of_mem_degreeLT
      (genL_mem_degreeLT κ a b (semi_mem_degreeLT_succ κ a b t p)) (not_lt.1 hk)]
    exact hasDerivAt_const _ _

@[simp] theorem semi_zero_time (p : ℝ[X]) : semi κ a b 0 p = p := by
  simp only [semi, zero_smul, NormedSpace.exp_zero, vecOf]
  rw [one_apply_eq_self, LinearEquiv.symm_apply_apply]

theorem semi_eq_of_isFlow {y : ℝ → ℝ[X]} (hy : IsFlow κ a b y) (t : ℝ) :
    semi κ a b t (y 0) = y t := by
  have := (isFlow_semi κ a b (y 0)).eq hy (by simp)
  exact congrFun this t

theorem semi_add (t : ℝ) (p q : ℝ[X]) : semi κ a b t (p + q) = semi κ a b t p + semi κ a b t q := by
  have h := semi_eq_of_isFlow κ a b ((isFlow_semi κ a b p).add (isFlow_semi κ a b q)) t
  simpa using h

theorem semi_smul (t c : ℝ) (p : ℝ[X]) : semi κ a b t (c • p) = c • semi κ a b t p := by
  have h := semi_eq_of_isFlow κ a b ((isFlow_semi κ a b p).smul c) t
  simpa using h

/-- The semigroup as a linear map. -/
def semiL (t : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := semi κ a b t
  map_add' := semi_add κ a b t
  map_smul' c p := semi_smul κ a b t c p

@[simp] theorem semiL_apply (t : ℝ) (p : ℝ[X]) : semiL κ a b t p = semi κ a b t p := rfl

theorem semi_C (t c : ℝ) : semi κ a b t (C c) = C c := by
  have h := semi_eq_of_isFlow κ a b (isFlow_const (κ := κ) (a := a) (b := b) (genL_C κ a b c)) t
  simpa using h

theorem semi_one (t : ℝ) : semi κ a b t 1 = 1 := by
  simpa using semi_C κ a b t 1

theorem semi_C_mul (t c : ℝ) (p : ℝ[X]) : semi κ a b t (C c * p) = C c * semi κ a b t p := by
  rw [← smul_eq_C_mul, semi_smul, smul_eq_C_mul]

/-- **The semigroup law.** -/
theorem semi_semi (s t : ℝ) (p : ℝ[X]) : semi κ a b s (semi κ a b t p) = semi κ a b (s + t) p := by
  have hz := (isFlow_semi κ a b p).comp_add t
  have h := semi_eq_of_isFlow κ a b hz s
  simpa using h

theorem semi_mem_degreeLT {n : ℕ} {p : ℝ[X]} (hp : p ∈ degreeLT ℝ n) (t : ℝ) :
    semi κ a b t p ∈ degreeLT ℝ n := by
  rcases eq_or_ne p 0 with rfl | h0
  · have : semi κ a b t 0 = 0 := by simpa using semi_smul κ a b t 0 0
    rw [this]; exact Submodule.zero_mem _
  have hd : p.natDegree + 1 ≤ n := by
    have := mem_degreeLT.1 hp
    rw [degree_eq_natDegree h0] at this
    exact_mod_cast this
  exact degreeLT_mono hd (semi_mem_degreeLT_succ κ a b t p)

/-- The coefficients of `T (y t)` for a linear map `T`, through the first `n` monomials. -/
theorem coeff_linearMap_of_mem {n : ℕ} {q : ℝ[X]} (hq : q ∈ degreeLT ℝ n) (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (k : ℕ) : (T q).coeff k = ∑ i ∈ Finset.range n, q.coeff i * (T (X ^ i)).coeff k := by
  conv_lhs => rw [eq_sum_of_mem_degreeLT hq]
  simp only [map_sum, ← smul_eq_C_mul, map_smul, finsetSum_coeff, coeff_smul, smul_eq_mul]

variable {κ a b}

/-- A linear map commuting with `L` maps flows to flows. -/
theorem IsFlow.map {y : ℝ → ℝ[X]} (hy : IsFlow κ a b y) (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hT : ∀ p, T (genL κ a b p) = genL κ a b (T p)) {m : ℕ}
    (hTm : ∀ t, T (y t) ∈ degreeLT ℝ m) : IsFlow κ a b (fun t => T (y t)) := by
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨m, hTm, fun t k => ?_⟩
  have e1 : ∀ s, (T (y s)).coeff k = ∑ i ∈ Finset.range n, (y s).coeff i * (T (X ^ i)).coeff k :=
    fun s => coeff_linearMap_of_mem (hn s) T k
  simp only [e1]
  have e2 : (genL κ a b (T (y t))).coeff k =
      ∑ i ∈ Finset.range n, (genL κ a b (y t)).coeff i * (T (X ^ i)).coeff k := by
    rw [← hT]
    exact coeff_linearMap_of_mem (genL_mem_degreeLT κ a b (hn t)) T k
  rw [e2]
  exact HasDerivAt.fun_sum fun i _ => (hy t i).mul_const _

variable (κ a b)

/-- **`L` commutes with the semigroup.** -/
theorem semi_genL (t : ℝ) (p : ℝ[X]) : semi κ a b t (genL κ a b p) = genL κ a b (semi κ a b t p) := by
  have hz := (isFlow_semi κ a b p).map (genL κ a b) (fun _ => rfl)
    (m := p.natDegree + 1) (fun t => genL_mem_degreeLT κ a b (semi_mem_degreeLT_succ κ a b t p))
  have h := semi_eq_of_isFlow κ a b hz t
  simpa using h

theorem hasDerivAt_coeff_semi (p : ℝ[X]) (t : ℝ) (k : ℕ) :
    HasDerivAt (fun s => (semi κ a b s p).coeff k) ((genL κ a b (semi κ a b t p)).coeff k) t := by
  obtain ⟨n, -, h⟩ := isFlow_semi κ a b p
  exact h t k

/-- The evaluation of a polynomial of degree `< n` through its first `n` coefficients. -/
theorem eval_eq_sum_of_mem {n : ℕ} {q : ℝ[X]} (hq : q ∈ degreeLT ℝ n) (x : ℝ) :
    q.eval x = ∑ i ∈ Finset.range n, q.coeff i * x ^ i := by
  conv_lhs => rw [eq_sum_of_mem_degreeLT hq]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

/-- **The time derivative of `(semi t p).eval x`** is `(L (semi t p)).eval x`. -/
theorem hasDerivAt_eval_semi (p : ℝ[X]) (x t : ℝ) :
    HasDerivAt (fun s => (semi κ a b s p).eval x) ((genL κ a b (semi κ a b t p)).eval x) t := by
  set N := p.natDegree + 1
  have e1 : ∀ s, (semi κ a b s p).eval x =
      ∑ i ∈ Finset.range N, (semi κ a b s p).coeff i * x ^ i :=
    fun s => eval_eq_sum_of_mem (semi_mem_degreeLT_succ κ a b s p) x
  simp only [e1]
  rw [eval_eq_sum_of_mem (genL_mem_degreeLT κ a b (semi_mem_degreeLT_succ κ a b t p)) x]
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_coeff_semi κ a b p t i).mul_const _

theorem continuous_eval_semi (p : ℝ[X]) (x : ℝ) : Continuous fun s => (semi κ a b s p).eval x :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_eval_semi κ a b p x t).continuousAt

theorem continuous_coeff_semi (p : ℝ[X]) (k : ℕ) : Continuous fun s => (semi κ a b s p).coeff k :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_coeff_semi κ a b p t k).continuousAt

/-- Joint continuity of `(t, x) ↦ (semi t p).eval x`. -/
theorem continuous_eval_semi_uncurry (p : ℝ[X]) :
    Continuous fun z : ℝ × ℝ => (semi κ a b z.1 p).eval z.2 := by
  set N := p.natDegree + 1
  have e1 : ∀ z : ℝ × ℝ, (semi κ a b z.1 p).eval z.2 =
      ∑ i ∈ Finset.range N, (semi κ a b z.1 p).coeff i * z.2 ^ i :=
    fun z => eval_eq_sum_of_mem (semi_mem_degreeLT_succ κ a b z.1 p) z.2
  simp only [e1]
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_coeff_semi κ a b p i).comp continuous_fst).mul (continuous_snd.pow i)

end JacobiExists

end Sec2

end InteractingSLE
