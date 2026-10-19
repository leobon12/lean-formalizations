import HigherDimLFPP.Var.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Piecewise-affine profiles: energy, increments, and the padding `ψ_K` (source §5.1)

Deterministic facts about the profiles of `V_n(E)` (frozen `Vg`) used by Lemma 5.1 (packet P-L1,
target T1; audit HA4, "Details for later use" D1), for an arbitrary real inner product space `E`
(the source uses `E = ℝ^{d-1}`).

* The basic structure of `V_n(E)` is reused from `HigherDimLFPP/Var/Basic.lean` (packet P-V):
  `Var.Vg_piece`, `Var.Vg_hasDerivAt`, `Var.Vg_energy`, `Var.Vg_mono`, `Var.energy_nonneg`.
* `incr K f i = f((i+1)/K) - f(i/K)`; `energy_eq_sum`: the discrete energy
  `E(f) = (2ⁿ/2) Σ_k ‖f((k+1)/2ⁿ) - f(k/2ⁿ)‖²` in terms of `incr` (from `Var.Vg_energy`);
  `incr_block`: on the refined mesh `K = 2^{n+g}` the increments of `f ∈ V_n(E)` are constant on
  blocks of `2^g` intervals.
* `norm_node_le`: `‖f(i/K)‖ ≤ E(f)^{1/2}` (Cauchy–Schwarz from both endpoints; HA4 D1 item 6).
* `norm_incr_le`: `‖f((i+1)/K) - f(i/K)‖ ≤ (2 E(f) 2ⁿ)^{1/2} / K` (HA4 D1, "Increments").
* `psiK K`: the source's `ψ_K`, affine on the intervals of length `1/K`, `1/K` at odd and `0`
  at even mesh points of `[0,1]`, and zero outside `[0,1]`.
* `padProf K f v a = f + a ψ_K v`; for `K = 2^{n+g}`, `g ≥ 1` and `‖v‖ = 1`:
  `padProf_mem_Vg` (`f + a ψ_K v ∈ V_{n+g}(E)`), the discrete energy identity
  `sum_sq_incr_padProf`, and (5.3), `energy_padProf : E(f + a ψ_K v) = E(f) + a²/2`.

2D source: `LQGDimension/Section2/Bounds.lean` (`V_node_abs_le`), for scalar profiles on the
mesh `16⁻ⁿ`; here the profiles are vector valued and the mesh is dyadic.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Increments -/

/-- Increment of `f` on the `i`-th interval of the mesh `1/K`. -/
def incr (K : ℕ) (f : ℝ → E) (i : ℕ) : E := f (((i : ℝ) + 1) / K) - f ((i : ℝ) / K)

omit [InnerProductSpace ℝ E] in
theorem incr_pow (n : ℕ) (f : ℝ → E) (k : ℕ) :
    incr (2 ^ n) f k = f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n) := by
  simp only [incr, Nat.cast_pow, Nat.cast_ofNat]

omit [InnerProductSpace ℝ E] in
theorem incr_add (K : ℕ) (f g : ℝ → E) (i : ℕ) :
    incr K (fun x => f x + g x) i = incr K f i + incr K g i := by
  simp only [incr]
  abel

theorem incr_smul_const (K : ℕ) (c : ℝ → ℝ) (v : E) (i : ℕ) :
    incr K (fun x => c x • v) i = incr K c i • v := by
  simp only [incr, sub_smul]

/-- **Discrete energy.** `E(f) = (2ⁿ/2) Σ_{k<2ⁿ} ‖f((k+1)/2ⁿ) - f(k/2ⁿ)‖²` on `V_n(E)`
(`Var.Vg_energy`, written with `incr`). -/
theorem energy_eq_sum {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) :
    energy f = ((2 : ℝ) ^ n / 2) * ∑ k ∈ Finset.range (2 ^ n), ‖incr (2 ^ n) f k‖ ^ 2 := by
  rw [Var.Vg_energy hf]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [incr_pow]

/-- On the refined mesh `K = 2^{n+g}`, the increments of `f ∈ V_n(E)` are constant on blocks of
`2^g` consecutive intervals. -/
theorem incr_block {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) (g : ℕ) {i : ℕ}
    (hi : i < 2 ^ (n + g)) :
    incr (2 ^ (n + g)) f i = ((2 : ℝ) ^ g)⁻¹ • incr (2 ^ n) f (i / 2 ^ g) := by
  have hpos : 0 < 2 ^ g := by positivity
  set k := i / 2 ^ g with hk
  have hklt : k < 2 ^ n := by
    rw [hk, Nat.div_lt_iff_lt_mul hpos, ← pow_add]
    exact hi
  have h1 : k * 2 ^ g ≤ i := Nat.div_mul_le_self i (2 ^ g)
  have h2 : i + 1 ≤ (k + 1) * 2 ^ g := by
    have := Nat.lt_div_mul_add (a := i) hpos
    rw [← hk] at this
    linarith
  have h1' : (k : ℝ) * 2 ^ g ≤ i := by exact_mod_cast h1
  have h2' : (i : ℝ) + 1 ≤ ((k : ℝ) + 1) * 2 ^ g := by exact_mod_cast h2
  have hL : (0 : ℝ) < 2 ^ n := by positivity
  have hG : (0 : ℝ) < 2 ^ g := by positivity
  have hmem : ∀ y : ℝ, (k : ℝ) * 2 ^ g ≤ y → y ≤ ((k : ℝ) + 1) * 2 ^ g →
      y / 2 ^ (n + g) ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n) := by
    intro y hy1 hy2
    rw [pow_add]
    constructor
    · rw [div_le_div_iff₀ hL (by positivity)]
      nlinarith
    · rw [div_le_div_iff₀ (by positivity) hL]
      nlinarith
  have hA := Var.Vg_piece hf hklt (hmem (i : ℝ) h1' (by linarith))
  have hB := Var.Vg_piece hf hklt (hmem ((i : ℝ) + 1) (by linarith) h2')
  rw [incr_pow, incr_pow, hA, hB, add_sub_add_left_eq_sub, ← sub_smul]
  congr 1
  rw [pow_add]
  field_simp
  ring

/-- For `g ≥ 1`, the two halves `2j`, `2j+1` of a pair lie in the same block. -/
theorem incr_two_mul_eq {n g : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) (hg : 1 ≤ g) {j : ℕ}
    (hj : 2 * j + 1 < 2 ^ (n + g)) :
    incr (2 ^ (n + g)) f (2 * j) = incr (2 ^ (n + g)) f (2 * j + 1) := by
  rw [incr_block hf g (by omega), incr_block hf g hj]
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  have e1 : 2 * j / 2 ^ (g' + 1) = j / 2 ^ g' := by
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    congr 1
    omega
  have e2 : (2 * j + 1) / 2 ^ (g' + 1) = j / 2 ^ g' := by
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    congr 1
    omega
  rw [e1, e2]

/-! ## Node values and increments -/

omit [InnerProductSpace ℝ E] in
theorem sum_incr_range (K : ℕ) (f : ℝ → E) (i : ℕ) :
    ∑ k ∈ Finset.range i, incr K f k = f ((i : ℝ) / K) - f 0 := by
  have h := Finset.sum_range_sub (fun k : ℕ => f ((k : ℝ) / K)) i
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at h
  exact h

omit [InnerProductSpace ℝ E] in
/-- Cauchy–Schwarz: `‖Σ_{k∈s} x_k‖² ≤ |s| Σ_{k∈s} ‖x_k‖²`. -/
theorem norm_sum_sq_le {ι : Type*} (s : Finset ι) (x : ι → E) :
    ‖∑ k ∈ s, x k‖ ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, ‖x k‖ ^ 2 := by
  have h1 : ‖∑ k ∈ s, x k‖ ≤ ∑ k ∈ s, ‖x k‖ := norm_sum_le s x
  have h2 : (∑ k ∈ s, ‖x k‖) ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, ‖x k‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc ‖∑ k ∈ s, x k‖ ^ 2 ≤ (∑ k ∈ s, ‖x k‖) ^ 2 := by gcongr
    _ ≤ _ := h2

/-- **Node bound** (HA4 D1, item 6): `‖f(i/K)‖ ≤ E(f)^{1/2}` for `f ∈ V_m(E)`, `K = 2^m`. -/
theorem norm_node_le {m K : ℕ} (hK : K = 2 ^ m) {f : ℝ → E} (hf : f ∈ Vg E m) {i : ℕ}
    (hi : i ≤ K) : ‖f ((i : ℝ) / K)‖ ≤ √(energy f) := by
  have hKpos : (0 : ℝ) < K := by rw [hK]; positivity
  have hE : energy f = ((K : ℝ) / 2) * ∑ k ∈ Finset.range K, ‖incr K f k‖ ^ 2 := by
    rw [energy_eq_sum hf, hK]; push_cast; ring
  set A := ∑ k ∈ Finset.range i, ‖incr K f k‖ ^ 2 with hA
  set B := ∑ k ∈ Finset.Ico i K, ‖incr K f k‖ ^ 2 with hB
  have hAB : A + B = ∑ k ∈ Finset.range K, ‖incr K f k‖ ^ 2 :=
    Finset.sum_range_add_sum_Ico _ hi
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hf0 : f 0 = 0 := hf.1
  have hf1 : f ((K : ℝ) / K) = 0 := by rw [div_self hKpos.ne']; exact hf.2.1
  -- from the left endpoint
  have hL : ‖f ((i : ℝ) / K)‖ ^ 2 ≤ (i : ℝ) * A := by
    have := norm_sum_sq_le (Finset.range i) (incr K f)
    rw [sum_incr_range, hf0, sub_zero, Finset.card_range] at this
    exact this
  -- from the right endpoint
  have hR : ‖f ((i : ℝ) / K)‖ ^ 2 ≤ ((K : ℝ) - i) * B := by
    have hsum : ∑ k ∈ Finset.Ico i K, incr K f k = -f ((i : ℝ) / K) := by
      have h := Finset.sum_range_add_sum_Ico (incr K f) hi
      rw [sum_incr_range, sum_incr_range, hf0, hf1] at h
      rw [← sub_eq_of_eq_add' h.symm]
      abel
    have := norm_sum_sq_le (Finset.Ico i K) (incr K f)
    rw [hsum, norm_neg, Nat.card_Ico] at this
    have hcast : ((K - i : ℕ) : ℝ) = (K : ℝ) - i := by
      rw [Nat.cast_sub hi]
    rw [hcast] at this
    exact this
  have hsq : ‖f ((i : ℝ) / K)‖ ^ 2 ≤ energy f := by
    rw [hE, ← hAB]
    have hi' : (i : ℝ) ≤ K := by exact_mod_cast hi
    rcases le_or_gt (2 * (i : ℝ)) K with h2 | h2
    · calc ‖f ((i : ℝ) / K)‖ ^ 2 ≤ (i : ℝ) * A := hL
        _ ≤ ((K : ℝ) / 2) * A := by gcongr; linarith
        _ ≤ ((K : ℝ) / 2) * (A + B) := by gcongr; linarith
    · calc ‖f ((i : ℝ) / K)‖ ^ 2 ≤ ((K : ℝ) - i) * B := hR
        _ ≤ ((K : ℝ) / 2) * B := by gcongr; linarith
        _ ≤ ((K : ℝ) / 2) * (A + B) := by gcongr; linarith
  exact Real.le_sqrt_of_sq_le hsq

/-- **Increment bound** (HA4 D1, "Increments"): on the mesh `K = 2^{n+g}`,
`‖f((i+1)/K) - f(i/K)‖ ≤ (2 E(f) 2ⁿ)^{1/2} / K` for `f ∈ V_n(E)`. -/
theorem norm_incr_le {n g : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) {i : ℕ} (hi : i < 2 ^ (n + g)) :
    ‖incr (2 ^ (n + g)) f i‖ ≤ √(2 * energy f * 2 ^ n) / (2 ^ (n + g) : ℕ) := by
  have hpos : 0 < 2 ^ g := by positivity
  set k := i / 2 ^ g with hk
  have hklt : k < 2 ^ n := by
    rw [hk, Nat.div_lt_iff_lt_mul hpos, ← pow_add]
    exact hi
  have hL : (0 : ℝ) < 2 ^ n := by positivity
  have hG : (0 : ℝ) < 2 ^ g := by positivity
  have hcoarse : ‖incr (2 ^ n) f k‖ ^ 2 ≤ 2 * energy f / 2 ^ n := by
    have h1 : ‖incr (2 ^ n) f k‖ ^ 2 ≤ ∑ k ∈ Finset.range (2 ^ n), ‖incr (2 ^ n) f k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖incr (2 ^ n) f k‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_range.2 hklt)
    rw [energy_eq_sum hf]
    rw [le_div_iff₀ hL]
    nlinarith
  rw [incr_block hf g hi, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hG]
  have hrhs : √(2 * energy f * 2 ^ n) / ((2 ^ (n + g) : ℕ) : ℝ) =
      √(2 * energy f / 2 ^ n) / 2 ^ g := by
    have hE0 : 0 ≤ energy f := Var.energy_nonneg f
    push_cast
    rw [pow_add]
    have h2n : √(2 * energy f * 2 ^ n) = √(2 * energy f / 2 ^ n) * 2 ^ n := by
      rw [show 2 * energy f * 2 ^ n = (2 * energy f / 2 ^ n) * (2 ^ n) ^ 2 by
        field_simp]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hL.le]
    rw [h2n]
    field_simp
  rw [hrhs, inv_mul_eq_div]
  gcongr
  exact Real.le_sqrt_of_sq_le hcoarse

/-! ## The padding function `ψ_K` -/

/-- The source's `ψ_K` (§5.1): affine on the intervals of length `1/K`, with value `1/K` at odd
and `0` at even mesh points of `[0,1]`; extended by zero outside `[0,1]`. -/
def psiK (K : ℕ) (x : ℝ) : ℝ :=
  if x ∈ Icc (0 : ℝ) 1 then |(K : ℝ) * x - 2 * round ((K : ℝ) * x / 2)| / K else 0

/-- The triangle wave `y ↦ |y - 2 round(y/2)|` is affine on `[i, i+1]`. -/
theorem tri_eq (i : ℕ) {y : ℝ} (hy : y ∈ Icc (i : ℝ) ((i : ℝ) + 1)) :
    |y - 2 * round (y / 2)| = if Even i then y - i else (i : ℝ) + 1 - y := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
  · subst hk
    have hev : Even (2 * k) := even_two_mul k
    rw [ite_eq_left hev]
    push_cast at hy ⊢
    rcases lt_or_eq_of_le hy.2 with hlt | heq
    · have hr : round (y / 2) = (k : ℤ) := by
        rw [round_eq, Int.floor_eq_iff]
        push_cast
        constructor <;> linarith [hy.1]
      rw [hr]
      push_cast
      rw [abs_of_nonneg (by linarith [hy.1])]
    · have hr : round (y / 2) = (k : ℤ) + 1 := by
        rw [round_eq, Int.floor_eq_iff]
        push_cast
        constructor <;> linarith
      rw [hr, heq]
      push_cast
      rw [show 2 * (k : ℝ) + 1 - 2 * ((k : ℝ) + 1) = -1 by ring, abs_neg, abs_one]
      ring
  · subst hk
    have hodd : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)
    rw [ite_eq_right hodd]
    push_cast at hy ⊢
    have hr : round (y / 2) = (k : ℤ) + 1 := by
      rw [round_eq, Int.floor_eq_iff]
      push_cast
      constructor <;> linarith [hy.1, hy.2]
    rw [hr]
    push_cast
    rw [abs_of_nonpos (by linarith [hy.2])]
    ring

theorem psiK_of_not_mem {K : ℕ} {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) : psiK K x = 0 := by
  simp [psiK, hx]

/-- `ψ_K` on the `i`-th mesh interval. -/
theorem psiK_affine {K : ℕ} (hK : 0 < K) {i : ℕ} (hi : i < K) {x : ℝ}
    (hx : x ∈ Icc ((i : ℝ) / K) (((i : ℝ) + 1) / K)) :
    psiK K x = if Even i then ((K : ℝ) * x - i) / K else ((i : ℝ) + 1 - K * x) / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hi' : (i : ℝ) + 1 ≤ K := by exact_mod_cast hi
  have hx01 : x ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact le_trans (by positivity) hx.1
    · calc x ≤ ((i : ℝ) + 1) / K := hx.2
        _ ≤ 1 := by rw [div_le_one hK']; exact hi'
  have hy : (K : ℝ) * x ∈ Icc (i : ℝ) ((i : ℝ) + 1) := by
    constructor
    · have := hx.1; rw [div_le_iff₀ hK'] at this; linarith
    · have := hx.2; rw [le_div_iff₀ hK'] at this; linarith
  rw [psiK, ite_eq_left hx01, tri_eq i hy]
  split_ifs <;> rfl

theorem psiK_zero (K : ℕ) : psiK K 0 = 0 := by
  simp [psiK]

theorem psiK_one {K : ℕ} (hK : Even K) : psiK K 1 = 0 := by
  obtain ⟨k, rfl⟩ := hK
  have h01 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hr : round (((k + k : ℕ) : ℝ) * 1 / 2) = (k : ℤ) := by
    rw [show ((k + k : ℕ) : ℝ) * 1 / 2 = ((k : ℤ) : ℝ) by push_cast; ring, round_intCast]
  rw [psiK, ite_eq_left h01, hr]
  have : ((k + k : ℕ) : ℝ) * 1 - 2 * ((k : ℤ) : ℝ) = 0 := by push_cast; ring
  rw [this, abs_zero, zero_div]

/-- Mesh values of `ψ_K`: `0` at even and `1/K` at odd mesh points. -/
theorem psiK_node {K : ℕ} (hK : 0 < K) (hKe : Even K) {i : ℕ} (hi : i ≤ K) :
    psiK K ((i : ℝ) / K) = if Even i then 0 else (1 : ℝ) / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rcases lt_or_eq_of_le hi with hlt | heq
  · rw [psiK_affine hK hlt ⟨le_refl _, by gcongr; linarith⟩]
    split_ifs
    · field_simp; ring
    · field_simp; ring
  · subst heq
    rw [div_self hK'.ne', psiK_one hKe, ite_eq_left hKe]

/-- Increments of `ψ_K`: `+1/K` on even and `-1/K` on odd mesh intervals. -/
theorem incr_psiK {K : ℕ} (hK : 0 < K) {i : ℕ} (hi : i < K) :
    incr K (psiK K) i = if Even i then (1 : ℝ) / K else (-1 : ℝ) / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hle : (i : ℝ) / K ≤ ((i : ℝ) + 1) / K := by gcongr; linarith
  rw [incr, psiK_affine hK hi (right_mem_Icc.2 hle), psiK_affine hK hi (left_mem_Icc.2 hle)]
  split_ifs
  · field_simp; ring
  · field_simp; ring

theorem abs_psiK_le (K : ℕ) (x : ℝ) : |psiK K x| ≤ (1 : ℝ) / K := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp [psiK]
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · -- `x` lies in some mesh interval
    set i := min ⌊(K : ℝ) * x⌋₊ (K - 1) with hi_def
    have hiK : i < K := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hK one_pos)
    have hxi : x ∈ Icc ((i : ℝ) / K) (((i : ℝ) + 1) / K) := by
      have hKx : 0 ≤ (K : ℝ) * x := mul_nonneg hK'.le hx.1
      rcases le_or_gt ⌊(K : ℝ) * x⌋₊ (K - 1) with h | h
      · have hi : i = ⌊(K : ℝ) * x⌋₊ := min_eq_left h
        rw [hi]
        constructor
        · rw [div_le_iff₀ hK']; linarith [Nat.floor_le hKx]
        · rw [le_div_iff₀ hK']; linarith [Nat.lt_floor_add_one ((K : ℝ) * x)]
      · have hi : i = K - 1 := min_eq_right h.le
        have hge : (K : ℝ) - 1 ≤ (K : ℝ) * x := by
          have h1 : K ≤ ⌊(K : ℝ) * x⌋₊ := by omega
          have h2 : (K : ℝ) ≤ ⌊(K : ℝ) * x⌋₊ := by exact_mod_cast h1
          linarith [Nat.floor_le hKx]
        rw [hi, Nat.cast_sub (by omega : 1 ≤ K)]
        push_cast
        constructor
        · rw [div_le_iff₀ hK']; nlinarith [hx.2]
        · rw [le_div_iff₀ hK']; nlinarith [hx.2]
    rw [psiK_affine hK hiK hxi]
    have h1 := hxi.1
    have h2 := hxi.2
    rw [div_le_iff₀ hK'] at h1
    rw [le_div_iff₀ hK'] at h2
    have key : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |t / K| ≤ (1 : ℝ) / K := by
      intro t ht0 ht1
      rw [abs_of_nonneg (div_nonneg ht0 hK'.le)]
      exact div_le_div_of_nonneg_right ht1 hK'.le
    split_ifs
    · exact key _ (by linarith) (by linarith)
    · exact key _ (by linarith) (by linarith)
  · rw [psiK_of_not_mem hx, abs_zero]
    positivity

/-! ## Padded profiles `f + a ψ_K v` -/

/-- The padded profile `f + a ψ_K v` (source §5.1). -/
def padProf (K : ℕ) (f : ℝ → E) (v : E) (a : ℝ) (x : ℝ) : E := f x + (a * psiK K x) • v

theorem incr_padProf (K : ℕ) (f : ℝ → E) (v : E) (a : ℝ) (i : ℕ) :
    incr K (padProf K f v a) i = incr K f i + (a * incr K (psiK K) i) • v := by
  simp only [incr, padProf]
  rw [mul_sub, sub_smul]
  abel

/-- `f + a ψ_K v ∈ V_{n+g}(E)` for `f ∈ V_n(E)` and `g ≥ 1`. -/
theorem padProf_mem_Vg {n g : ℕ} (hg : 1 ≤ g) {f : ℝ → E} (hf : f ∈ Vg E n) (v : E) (a : ℝ) :
    padProf (2 ^ (n + g)) f v a ∈ Vg E (n + g) := by
  have hf' : f ∈ Vg E (n + g) := Var.Vg_mono (by omega) hf
  have hKpos : 0 < 2 ^ (n + g) := by positivity
  have hKe : Even (2 ^ (n + g)) := (Nat.even_pow' (by omega)).2 even_two
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [padProf, hf.1, psiK_zero, mul_zero, zero_smul, add_zero]
  · simp only [padProf, hf.2.1, psiK_one hKe, mul_zero, zero_smul, add_zero]
  · intro x hx
    simp only [padProf, hf.2.2.1 x hx, psiK_of_not_mem hx, mul_zero, zero_smul, add_zero]
  · intro k hk
    obtain ⟨α, β, h⟩ := hf'.2.2.2 k hk
    have hK' : (0 : ℝ) < ((2 ^ (n + g) : ℕ) : ℝ) := by exact_mod_cast hKpos
    set K : ℕ := 2 ^ (n + g) with hK
    have hcast : ((2 : ℝ) ^ (n + g)) = (K : ℝ) := by rw [hK]; push_cast; ring
    by_cases he : Even k
    · refine ⟨α + (a * 1) • v, β + (a * (-(k : ℝ) / K)) • v, fun x hx => ?_⟩
      have hx' : x ∈ Icc ((k : ℝ) / K) (((k : ℝ) + 1) / K) := by rwa [← hcast]
      simp only [padProf, h x hx, psiK_affine hKpos hk hx', ite_eq_left he]
      rw [smul_add, smul_smul]
      have : (a * (((K : ℝ) * x - k) / K)) = x * (a * 1) + a * (-(k : ℝ) / K) := by
        field_simp
        ring
      rw [this, add_smul, ← smul_smul]
      abel
    · refine ⟨α + (a * (-1)) • v, β + (a * (((k : ℝ) + 1) / K)) • v, fun x hx => ?_⟩
      have hx' : x ∈ Icc ((k : ℝ) / K) (((k : ℝ) + 1) / K) := by rwa [← hcast]
      simp only [padProf, h x hx, psiK_affine hKpos hk hx', ite_eq_right he]
      rw [smul_add, smul_smul]
      have : (a * (((k : ℝ) + 1 - K * x) / K)) = x * (a * (-1)) + a * (((k : ℝ) + 1) / K) := by
        field_simp
        ring
      rw [this, add_smul, ← smul_smul]
      abel

/-- Pairing of consecutive indices in a sum over `range (2 M)`. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (h : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), h i = ∑ j ∈ Finset.range m, (h (2 * j) + h (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

/-- The cross term of (5.3) vanishes: `Σ_i (ψ_K-increment)_i ⟪Δ_i f, v⟫ = 0`. -/
theorem sum_incr_psiK_inner {n g : ℕ} (hg : 1 ≤ g) {f : ℝ → E} (hf : f ∈ Vg E n) (v : E) :
    ∑ i ∈ Finset.range (2 ^ (n + g)),
      incr (2 ^ (n + g)) (psiK (2 ^ (n + g))) i * ⟪incr (2 ^ (n + g)) f i, v⟫ = 0 := by
  set K : ℕ := 2 ^ (n + g) with hK
  have hKpos : 0 < K := by positivity
  have hK2 : K = 2 * 2 ^ (n + g - 1) := by
    rw [hK, ← pow_succ']
    congr 1
    omega
  rw [hK2, sum_range_two_mul]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : 2 * j + 1 < K := by
    have := Finset.mem_range.1 hj
    omega
  rw [← hK2, incr_psiK hKpos (by omega), incr_psiK hKpos hj',
    incr_two_mul_eq hf hg (by rw [← hK]; exact hj')]
  have he : Even (2 * j) := even_two_mul j
  have ho : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one j)
  rw [ite_eq_left he, ite_eq_right ho]
  ring

/-- **Discrete energy identity** behind (5.3): on the mesh `K = 2^{n+g}`, `g ≥ 1`, `‖v‖ = 1`,
`Σ_i ‖Δ_i(f + a ψ_K v)‖² = Σ_i ‖Δ_i f‖² + a²/K`. -/
theorem sum_sq_incr_padProf {n g : ℕ} (hg : 1 ≤ g) {f : ℝ → E} (hf : f ∈ Vg E n) {v : E}
    (hv : ‖v‖ = 1) (a : ℝ) :
    ∑ i ∈ Finset.range (2 ^ (n + g)), ‖incr (2 ^ (n + g)) (padProf (2 ^ (n + g)) f v a) i‖ ^ 2 =
      ∑ i ∈ Finset.range (2 ^ (n + g)), ‖incr (2 ^ (n + g)) f i‖ ^ 2 +
        a ^ 2 / ((2 ^ (n + g) : ℕ) : ℝ) := by
  set K : ℕ := 2 ^ (n + g) with hK
  have hKpos : 0 < K := by positivity
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hterm : ∀ i ∈ Finset.range K, ‖incr K (padProf K f v a) i‖ ^ 2 =
      ‖incr K f i‖ ^ 2 + 2 * a * (incr K (psiK K) i * ⟪incr K f i, v⟫) + a ^ 2 / (K : ℝ) ^ 2 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [incr_padProf, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      hv, mul_one, sq_abs, incr_psiK hKpos hi']
    split_ifs
    · field_simp
    · field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hK, sum_incr_psiK_inner hg hf v, ← hK]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_zero, add_zero]
  field_simp

/-- **(5.3)**: `E(f + a ψ_K v) = E(f) + a²/2` for `f ∈ V_n(E)`, `K = 2^{n+g}`, `g ≥ 1`,
`‖v‖ = 1`. -/
theorem energy_padProf {n g : ℕ} (hg : 1 ≤ g) {f : ℝ → E} (hf : f ∈ Vg E n) {v : E}
    (hv : ‖v‖ = 1) (a : ℝ) :
    energy (padProf (2 ^ (n + g)) f v a) = energy f + a ^ 2 / 2 := by
  have hf' : f ∈ Vg E (n + g) := Var.Vg_mono (by omega) hf
  rw [energy_eq_sum (padProf_mem_Vg hg hf v a), energy_eq_sum hf', sum_sq_incr_padProf hg hf hv]
  have hK' : (0 : ℝ) < ((2 ^ (n + g) : ℕ) : ℝ) := by positivity
  push_cast at hK' ⊢
  field_simp

end HigherDimLFPP.Lower
