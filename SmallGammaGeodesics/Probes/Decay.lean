import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval

/-!
# The discrete decay lemma (GA2 D4.1)

For `n ≥ 1`, a `C^p` multiplier `m : ℝ → ℂ` vanishing for `|s| > R/n`, and `N ≥ R + p`, the finite
trigonometric sum `S(θ) = ∑_{|k| ≤ N} m(k/n) e^{ikθ}` (`trigSum n N m θ`) satisfies, for `|θ| ≤ π`,

* `‖S(θ)‖ ≤ (2R + 1) sup ‖m‖`, and
* `(2|θ|/π)^p ‖S(θ)‖ ≤ (2R + p + 1) sup ‖m^{(p)}‖ / n^p`

(`decay_lemma`, target T8 of packet P-B1). The second bound is GA2's
`|S(θ)| ≤ (2An+p+1) M_p n^{-p} (π/(2|θ|))^p` multiplied through, so that it has no junk value at
`θ = 0`; `decay_lemma'` is the divided form for `θ ≠ 0`.

The proof is summation by parts: `(1 - e^{iθ}) ∑ a_k e^{ikθ} = ∑ (a_k - a_{k-1}) e^{ikθ}`
(`one_sub_exp_mul_trigSum`), iterated `p` times (`one_sub_exp_pow_mul_trigSum`); the `p`-th backward
difference of the samples of `m` with step `1/n` is at most `n^{-p} sup ‖m^{(p)}‖`
(`norm_iterate_bwdDiff_le`, by the mean value theorem); at most `2R + p + 1` of them are nonzero; and
`‖1 - e^{iθ}‖ = 2|sin(θ/2)| ≥ 2|θ|/π` (`two_mul_abs_div_pi_le_norm_one_sub_exp`).

This file also contains the symmetrization `∑_{|k| ≤ N} f k = f 0 + ∑_{k=1}^N (f k + f (-k))`
(`sum_Icc_int_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset
open scoped Real

namespace SmallGammaGeodesics

/-! ### Sums over symmetric integer intervals -/

/-- Shifting the index of a sum over an integer interval. -/
theorem sum_Icc_int_sub_one (f : ℤ → ℂ) (a b : ℤ) :
    ∑ k ∈ Icc a b, f (k - 1) = ∑ k ∈ Icc (a - 1) (b - 1), f k := by
  rw [show a - 1 = a + (-1) by ring, show b - 1 = b + (-1) by ring, ← map_add_right_Icc,
    sum_map]
  rfl

/-- `Icc (-(N+1)) (N+1) = {-(N+1), N+1} ∪ Icc (-N) N` in `ℤ`. -/
theorem Icc_int_succ (N : ℕ) :
    Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
      insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Icc (-(N : ℤ)) N)) := by
  ext k
  simp only [mem_Icc, mem_insert]
  push_cast
  omega

/-- Symmetrization: `∑_{|k| ≤ N} f k = f 0 + ∑_{k=1}^N (f k + f (-k))`. -/
theorem sum_Icc_int_eq {M : Type*} [AddCommMonoid M] (f : ℤ → M) (N : ℕ) :
    ∑ k ∈ Icc (-(N : ℤ)) N, f k = f 0 + ∑ k ∈ Icc (1 : ℕ) N, (f k + f (-(k : ℤ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Icc_int_succ, sum_insert, sum_insert, ih, sum_Icc_succ_top (by omega)]
    · push_cast
      abel
    · simp only [mem_Icc]
      omega
    · simp only [mem_insert, mem_Icc]
      omega

/-! ### Backward differences and trigonometric sums -/

/-- Backward difference with step `h`: `(∇_h g)(x) = g(x) - g(x - h)`. -/
def bwdDiff (h : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ := g x - g (x - h)

/-- The finite trigonometric sum `S(θ) = ∑_{|k| ≤ N} g(k/n) e^{ikθ}`. -/
def trigSum (n N : ℕ) (g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Icc (-(N : ℤ)) N, g ((k : ℝ) / n) * Complex.exp ((k : ℂ) * θ * Complex.I)

theorem norm_exp_int_mul_I (k : ℤ) (θ : ℝ) : ‖Complex.exp ((k : ℂ) * θ * Complex.I)‖ = 1 := by
  have : (k : ℂ) * θ = ((k * θ : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- One step of summation by parts. -/
theorem one_sub_exp_mul_trigSum {n N : ℕ} (g : ℝ → ℂ) (θ : ℝ)
    (hlo : g (((-(N : ℤ) - 1 : ℤ) : ℝ) / n) = 0) (hhi : g (((N : ℤ) : ℝ) / n) = 0) :
    (1 - Complex.exp (θ * Complex.I)) * trigSum n N g θ = trigSum n N (bwdDiff (1 / n) g) θ := by
  set F : ℤ → ℂ := fun k => g ((k : ℝ) / n) * Complex.exp ((k : ℂ) * θ * Complex.I) with hF
  have hshift : ∑ k ∈ Icc (-(N : ℤ)) N, g ((k : ℝ) / n - 1 / n) *
      Complex.exp ((k : ℂ) * θ * Complex.I) =
      Complex.exp (θ * Complex.I) * ∑ k ∈ Icc (-(N : ℤ)) N, F (k - 1) := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [hF]
    have h1 : (k : ℝ) / n - 1 / n = ((k - 1 : ℤ) : ℝ) / n := by push_cast; ring
    have h2 : Complex.exp ((k : ℂ) * θ * Complex.I) =
        Complex.exp (θ * Complex.I) * Complex.exp (((k - 1 : ℤ) : ℂ) * θ * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h1, h2]
    ring
  have hbig : ∑ k ∈ Icc (-(N : ℤ)) N, F (k - 1) = ∑ k ∈ Icc (-(N : ℤ)) N, F k := by
    rw [sum_Icc_int_sub_one]
    have hsub1 : Icc (-(N : ℤ) - 1) ((N : ℤ) - 1) ⊆ Icc (-(N : ℤ) - 1) N := by
      intro k hk
      simp only [mem_Icc] at hk ⊢
      omega
    have hsub2 : Icc (-(N : ℤ)) N ⊆ Icc (-(N : ℤ) - 1) N := by
      intro k hk
      simp only [mem_Icc] at hk ⊢
      omega
    rw [sum_subset hsub1, sum_subset hsub2]
    · intro k hk hk'
      simp only [mem_Icc] at hk hk'
      have : k = -(N : ℤ) - 1 := by omega
      simp only [hF, this, hlo, zero_mul]
    · intro k hk hk'
      simp only [mem_Icc] at hk hk'
      have : k = (N : ℤ) := by omega
      simp only [hF, this, hhi, zero_mul]
  unfold trigSum bwdDiff
  simp only [sub_mul, sum_sub_distrib]
  rw [hshift, hbig]
  ring

/-- Support propagation: if `g` vanishes off `[a, b]`, then `∇_h^p g` vanishes off `[a, b + p h]`. -/
theorem iterate_bwdDiff_eq_zero {h : ℝ} (hh : 0 ≤ h) (a : ℝ) :
    ∀ (p : ℕ) (g : ℝ → ℂ) (b : ℝ), (∀ s, (s < a ∨ b < s) → g s = 0) →
      ∀ s, (s < a ∨ b + p * h < s) → (bwdDiff h)^[p] g s = 0 := by
  intro p
  induction p with
  | zero =>
    intro g b hg s hs
    simp only [Nat.cast_zero, zero_mul, add_zero] at hs
    exact hg s hs
  | succ p ih =>
    intro g b hg s hs
    rw [Function.iterate_succ_apply]
    refine ih (bwdDiff h g) (b + h) ?_ s ?_
    · intro t ht
      unfold bwdDiff
      rcases ht with ht | ht
      · rw [hg t (Or.inl ht), hg (t - h) (Or.inl (by linarith))]
        ring
      · rw [hg t (Or.inr (by linarith)), hg (t - h) (Or.inr (by linarith))]
        ring
    · push_cast at hs
      rcases hs with hs | hs
      · exact Or.inl hs
      · exact Or.inr (by linarith)

/-- Iterated summation by parts. -/
theorem one_sub_exp_pow_mul_trigSum {n : ℕ} (hn : 0 < n) {R N : ℕ} (θ : ℝ) :
    ∀ (p i : ℕ) (g : ℝ → ℂ),
      (∀ s : ℝ, (s < -((R : ℝ) / n) ∨ ((R + i : ℕ) : ℝ) / n < s) → g s = 0) →
      R + i + p ≤ N →
      (1 - Complex.exp (θ * Complex.I)) ^ p * trigSum n N g θ =
        trigSum n N ((bwdDiff (1 / n))^[p] g) θ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  intro p
  induction p with
  | zero => intro i g _ _; simp
  | succ p ih =>
    intro i g hg hN
    have hlo : g (((-(N : ℤ) - 1 : ℤ) : ℝ) / n) = 0 := by
      refine hg _ (Or.inl ?_)
      rw [neg_div', div_lt_div_iff_of_pos_right hn']
      have : (R : ℝ) ≤ N := by exact_mod_cast (show R ≤ N by omega)
      push_cast
      linarith
    have hhi : g (((N : ℤ) : ℝ) / n) = 0 := by
      refine hg _ (Or.inr ?_)
      rw [div_lt_div_iff_of_pos_right hn']
      push_cast
      exact_mod_cast (show R + i < N by omega)
    rw [pow_succ, mul_assoc, one_sub_exp_mul_trigSum g θ hlo hhi,
      ih (i + 1) (bwdDiff (1 / n) g) ?_ (by omega), ← Function.iterate_succ_apply]
    intro s hs
    have h1n : (0 : ℝ) ≤ 1 / n := by positivity
    have := iterate_bwdDiff_eq_zero h1n (-((R : ℝ) / n)) 1 g (((R + i : ℕ) : ℝ) / n) hg s
    simp only [Function.iterate_one, Nat.cast_one, one_mul] at this
    refine this ?_
    rcases hs with hs | hs
    · exact Or.inl hs
    · refine Or.inr ?_
      have : (((R + (i + 1) : ℕ) : ℝ) / n) = ((R + i : ℕ) : ℝ) / n + 1 / n := by
        push_cast
        ring
      linarith

/-- The `p`-th backward difference with step `h ≥ 0` of a `C^p` function is at most
`h^p sup ‖g^{(p)}‖` (mean value theorem, by induction on `p`). -/
theorem norm_iterate_bwdDiff_le {h : ℝ} (hh : 0 ≤ h) :
    ∀ (p : ℕ) (g : ℝ → ℂ) (M : ℝ), ContDiff ℝ p g → (∀ s, ‖iteratedDeriv p g s‖ ≤ M) →
      ∀ x, ‖(bwdDiff h)^[p] g x‖ ≤ h ^ p * M := by
  intro p
  induction p with
  | zero =>
    intro g M _ hM x
    simpa using hM x
  | succ p ih =>
    intro g M hg hM x
    rw [Function.iterate_succ_apply]
    have hgp : ContDiff ℝ p g := hg.of_le (by exact_mod_cast Nat.le_succ p)
    have hcd : ContDiff ℝ p (bwdDiff h g) := by
      unfold bwdDiff
      exact hgp.sub (hgp.comp (contDiff_id.sub contDiff_const))
    have hsh : ContDiff ℝ p (fun x => g (x - h)) := hgp.comp (contDiff_id.sub contDiff_const)
    have hder : ∀ s, iteratedDeriv p (bwdDiff h g) s =
        iteratedDeriv p g s - iteratedDeriv p g (s - h) := by
      intro s
      unfold bwdDiff
      rw [iteratedDeriv_fun_sub hgp.contDiffAt hsh.contDiffAt, iteratedDeriv_comp_sub_const p g h]
    have hdiff : Differentiable ℝ (iteratedDeriv p g) :=
      hg.differentiable_iteratedDeriv p (by exact_mod_cast Nat.lt_succ_self p)
    have hbound : ∀ s, ‖iteratedDeriv p (bwdDiff h g) s‖ ≤ h * M := by
      intro s
      rw [hder s]
      have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
        (f := iteratedDeriv p g) (C := M) (x := s - h) (y := s)
        (fun z _ => hdiff z) (fun z _ => by rw [← iteratedDeriv_succ]; exact hM z)
        convex_univ (Set.mem_univ _) (Set.mem_univ _)
      calc ‖iteratedDeriv p g s - iteratedDeriv p g (s - h)‖ ≤ M * ‖s - (s - h)‖ := this
        _ = h * M := by
          rw [show s - (s - h) = h by ring, Real.norm_of_nonneg hh, mul_comm]
    calc ‖(bwdDiff h)^[p] (bwdDiff h g) x‖ ≤ h ^ p * (h * M) := ih _ _ hcd hbound x
      _ = h ^ (p + 1) * M := by ring

/-- Counting bound: a trigonometric sum of a function vanishing off `[-R/n, (R+q)/n]` has at most
`2R + q + 1` nonzero terms. -/
theorem norm_trigSum_le_of_support {n N R q : ℕ} (hn : 0 < n) (hN : R + q ≤ N) (G : ℝ → ℂ)
    (B : ℝ) (θ : ℝ)
    (hG : ∀ s : ℝ, (s < -((R : ℝ) / n) ∨ ((R + q : ℕ) : ℝ) / n < s) → G s = 0)
    (hB : ∀ s, ‖G s‖ ≤ B) :
    ‖trigSum n N G θ‖ ≤ (2 * R + q + 1) * B := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : Icc (-(R : ℤ)) ((R + q : ℕ) : ℤ) ⊆ Icc (-(N : ℤ)) N := by
    intro k hk
    simp only [mem_Icc] at hk ⊢
    push_cast at hk ⊢
    omega
  unfold trigSum
  rw [← sum_subset hsub]
  · calc ‖∑ k ∈ Icc (-(R : ℤ)) ((R + q : ℕ) : ℤ),
          G ((k : ℝ) / n) * Complex.exp ((k : ℂ) * θ * Complex.I)‖
        ≤ ∑ k ∈ Icc (-(R : ℤ)) ((R + q : ℕ) : ℤ),
          ‖G ((k : ℝ) / n) * Complex.exp ((k : ℂ) * θ * Complex.I)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Icc (-(R : ℤ)) ((R + q : ℕ) : ℤ), B := by
          refine sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_exp_int_mul_I, mul_one]
          exact hB _
      _ = (2 * R + q + 1) * B := by
          rw [sum_const, Int.card_Icc, nsmul_eq_mul]
          congr 1
          have : ((R + q : ℕ) : ℤ) + 1 - -(R : ℤ) = ((2 * R + q + 1 : ℕ) : ℤ) := by
            push_cast
            ring
          rw [this, Int.toNat_natCast]
          push_cast
          ring
  · intro k hk hk'
    simp only [mem_Icc, not_and_or, not_le] at hk'
    rw [hG _ ?_, zero_mul]
    rcases hk' with hk' | hk'
    · refine Or.inl ?_
      rw [neg_div', div_lt_div_iff_of_pos_right hn']
      have : (k : ℝ) < -(R : ℝ) := by exact_mod_cast hk'
      linarith
    · refine Or.inr ?_
      rw [div_lt_div_iff_of_pos_right hn']
      exact_mod_cast hk'

/-- `‖1 - e^{iθ}‖ = 2|sin(θ/2)| ≥ 2|θ|/π` for `|θ| ≤ π`. -/
theorem two_mul_abs_div_pi_le_norm_one_sub_exp {θ : ℝ} (hθ : |θ| ≤ π) :
    2 * |θ| / π ≤ ‖1 - Complex.exp (θ * Complex.I)‖ := by
  rw [norm_sub_rev, mul_comm (θ : ℂ), Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul,
    Real.norm_two, Real.norm_eq_abs]
  have key : |θ| / π ≤ |Real.sin (θ / 2)| := by
    have h0 : 0 ≤ |θ| / 2 := by positivity
    have h1 : |θ| / 2 ≤ π / 2 := by linarith
    have := Real.mul_le_sin h0 h1
    have heq : |Real.sin (θ / 2)| = Real.sin (|θ| / 2) := by
      rcases le_total 0 θ with h | h
      · rw [abs_of_nonneg h, abs_of_nonneg]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [abs_of_nonneg h])
      · rw [abs_of_nonpos h, show -θ / 2 = -(θ / 2) by ring, Real.sin_neg, abs_of_nonpos]
        exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith)
          (by linarith [abs_of_nonpos h, Real.pi_pos])
    rw [heq]
    calc |θ| / π = 2 / π * (|θ| / 2) := by field_simp
      _ ≤ _ := this
  calc 2 * |θ| / π = 2 * (|θ| / π) := by ring
    _ ≤ 2 * |Real.sin (θ / 2)| := by linarith

/-- Vanishing of `m` for `|s| > R/n`, in the one-sided form used by the summation by parts. -/
theorem support_of_abs {n R : ℕ} {m : ℝ → ℂ} (hsupp : ∀ s : ℝ, (R : ℝ) / n < |s| → m s = 0) :
    ∀ s : ℝ, (s < -((R : ℝ) / n) ∨ ((R + 0 : ℕ) : ℝ) / n < s) → m s = 0 := by
  intro s hs
  refine hsupp s ?_
  rcases hs with hs | hs
  · rw [abs_of_neg (by linarith [show (0 : ℝ) ≤ R / n by positivity])]
    linarith
  · simp only [add_zero] at hs
    exact lt_of_lt_of_le hs (le_abs_self s)

/-- The sup bound of the decay lemma: `‖S(θ)‖ ≤ (2R+1) sup ‖m‖`. -/
theorem norm_trigSum_le_sup {n : ℕ} (hn : 0 < n) {R N : ℕ} (hN : R ≤ N) {m : ℝ → ℂ}
    (hsupp : ∀ s : ℝ, (R : ℝ) / n < |s| → m s = 0) {M₀ : ℝ} (hM₀ : ∀ s, ‖m s‖ ≤ M₀) (θ : ℝ) :
    ‖trigSum n N m θ‖ ≤ (2 * R + 1) * M₀ := by
  have := norm_trigSum_le_of_support (N := N) (R := R) (q := 0) hn (by omega) m M₀ θ
    (support_of_abs hsupp) hM₀
  simpa using this

/-- The derivative bound of the decay lemma:
`(2|θ|/π)^p ‖S(θ)‖ ≤ (2R+p+1) sup ‖m^{(p)}‖ / n^p` for `|θ| ≤ π`. -/
theorem pow_mul_norm_trigSum_le {n : ℕ} (hn : 0 < n) {p R N : ℕ} (hN : R + p ≤ N) {m : ℝ → ℂ}
    (hm : ContDiff ℝ p m) (hsupp : ∀ s : ℝ, (R : ℝ) / n < |s| → m s = 0)
    {Mp : ℝ} (hMp : ∀ s, ‖iteratedDeriv p m s‖ ≤ Mp) {θ : ℝ} (hθ : |θ| ≤ π) :
    (2 * |θ| / π) ^ p * ‖trigSum n N m θ‖ ≤ (2 * R + p + 1) * Mp / (n : ℝ) ^ p := by
  have hRdiv := support_of_abs hsupp
  have h1n : (0 : ℝ) ≤ 1 / n := by positivity
  have hpow := one_sub_exp_pow_mul_trigSum hn θ p 0 m hRdiv (by omega)
  have hsuppIt : ∀ s : ℝ, (s < -((R : ℝ) / n) ∨ ((R + p : ℕ) : ℝ) / n < s) →
      (bwdDiff (1 / n))^[p] m s = 0 := by
    intro s hs
    refine iterate_bwdDiff_eq_zero h1n (-((R : ℝ) / n)) p m ((R : ℝ) / n) ?_ s ?_
    · intro t ht
      refine hRdiv t ?_
      simpa using ht
    · rcases hs with hs | hs
      · exact Or.inl hs
      · refine Or.inr ?_
        have : ((R + p : ℕ) : ℝ) / n = (R : ℝ) / n + p * (1 / n) := by
          push_cast
          ring
        linarith
  have hbd := norm_iterate_bwdDiff_le h1n p m Mp hm hMp
  have hsum := norm_trigSum_le_of_support (q := p) hn hN _ _ θ hsuppIt hbd
  have hnorm : (2 * |θ| / π) ^ p ≤ ‖1 - Complex.exp (θ * Complex.I)‖ ^ p :=
    pow_le_pow_left₀ (by positivity) (two_mul_abs_div_pi_le_norm_one_sub_exp hθ) p
  calc (2 * |θ| / π) ^ p * ‖trigSum n N m θ‖
      ≤ ‖1 - Complex.exp (θ * Complex.I)‖ ^ p * ‖trigSum n N m θ‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖trigSum n N ((bwdDiff (1 / n))^[p] m) θ‖ := by rw [← norm_pow, ← norm_mul, hpow]
    _ ≤ (2 * R + p + 1) * ((1 / n) ^ p * Mp) := hsum
    _ = (2 * R + p + 1) * Mp / (n : ℝ) ^ p := by
        rw [one_div, inv_pow]
        field_simp

/-- **Discrete decay lemma (GA2 D4.1; target T8).** Let `n ≥ 1`, `R + p ≤ N`, and let
`m : ℝ → ℂ` be `C^p` with `m s = 0` for `|s| > R/n`, `‖m‖ ≤ M₀` and `‖m^{(p)}‖ ≤ Mp`. Then for
`|θ| ≤ π` the sum `S(θ) = ∑_{|k| ≤ N} m(k/n) e^{ikθ}` satisfies `‖S(θ)‖ ≤ (2R+1) M₀` and
`(2|θ|/π)^p ‖S(θ)‖ ≤ (2R+p+1) Mp / n^p`. -/
theorem decay_lemma {n : ℕ} (hn : 0 < n) {p R N : ℕ} (hN : R + p ≤ N) {m : ℝ → ℂ}
    (hm : ContDiff ℝ p m) (hsupp : ∀ s : ℝ, (R : ℝ) / n < |s| → m s = 0)
    {M₀ Mp : ℝ} (hM₀ : ∀ s, ‖m s‖ ≤ M₀) (hMp : ∀ s, ‖iteratedDeriv p m s‖ ≤ Mp)
    {θ : ℝ} (hθ : |θ| ≤ π) :
    ‖trigSum n N m θ‖ ≤ (2 * R + 1) * M₀ ∧
      (2 * |θ| / π) ^ p * ‖trigSum n N m θ‖ ≤ (2 * R + p + 1) * Mp / (n : ℝ) ^ p :=
  ⟨norm_trigSum_le_sup hn (by omega) hsupp hM₀ θ, pow_mul_norm_trigSum_le hn hN hm hsupp hMp hθ⟩

/-- The decay lemma in GA2's divided form, for `0 < |θ| ≤ π`:
`‖S(θ)‖ ≤ (2R+p+1) Mp n^{-p} (π/(2|θ|))^p`. -/
theorem decay_lemma' {n : ℕ} (hn : 0 < n) {p R N : ℕ} (hN : R + p ≤ N) {m : ℝ → ℂ}
    (hm : ContDiff ℝ p m) (hsupp : ∀ s : ℝ, (R : ℝ) / n < |s| → m s = 0)
    {Mp : ℝ} (hMp : ∀ s, ‖iteratedDeriv p m s‖ ≤ Mp)
    {θ : ℝ} (hθ : |θ| ≤ π) (hθ0 : θ ≠ 0) :
    ‖trigSum n N m θ‖ ≤ (2 * R + p + 1) * Mp * ((n : ℝ)⁻¹) ^ p * (π / (2 * |θ|)) ^ p := by
  have hθpos : 0 < |θ| := abs_pos.mpr hθ0
  have h := pow_mul_norm_trigSum_le hn hN hm hsupp hMp hθ
  have hc : 0 < (2 * |θ| / π) ^ p := by positivity
  rw [← le_div_iff₀' hc] at h
  calc ‖trigSum n N m θ‖ ≤ (2 * R + p + 1) * Mp / (n : ℝ) ^ p / (2 * |θ| / π) ^ p := h
    _ = (2 * R + p + 1) * Mp * ((n : ℝ)⁻¹) ^ p * (π / (2 * |θ|)) ^ p := by
      rw [inv_pow, div_pow, div_pow]
      field_simp

end SmallGammaGeodesics
