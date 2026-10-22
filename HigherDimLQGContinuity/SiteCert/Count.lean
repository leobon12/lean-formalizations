import HigherDimLQGContinuity.SiteCert.Constants

/-!
# The catalogue size as a polynomial in `v⁻¹` (packet Q7b; Part B `b:lem-catalogue`, `b:lem-order`(d))

Source: blueprint Part B `b:lem-catalogue` ((4.9): per edge `N_tr` trials, three subsets of the `(2K_c + 1)^d` cells
and two padded leads of at most `N + 1` grid points of `(2K_l + 1)^d`), with `b:lem-order`(d) (ruling N29: every small
scale is `≥ c v^K`, `N ≤ C v^{-K}`). The frozen interface asks for `log J ≤ polyB A_p k_p 0 v⁻¹`.

* `q7b_log_card_le`: from the exact product bound `J ≤ (N_tr 8^{P} ((N + 1) Q^{N+1})²)^E` (packet Q4's
  `labelCatalogue_card_le`, `P = (2K_c + 1)^d`, `Q = (2K_l + 1)^d`):
  `log J ≤ E (N_tr + 3P + 2(N + 1) + 2(N + 1)Q)`.
* `q7b_count_le_polyB`: with `μ, ν ≥ c v^K` and `N ≤ C v^{-K}` (and `K_c = ⌈L/μ⌉₊ + 2`, `K_l = ⌈(5/2)/ν⌉₊ + 2`), the
  right side is at most `polyB (E (N_tr + 3(2L/c + 7)^d + 2(C + 1) + 2(C + 1)(5/c + 7)^d)) (K(d + 1)) 0 v⁻¹`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- **The logarithm of the catalogue product bound** ((4.9)): if
`J ≤ (N_tr (2^P)^3 ((N + 1) Q^{N+1})²)^E` with `P = (2K_c + 1)^d`, `Q = (2K_l + 1)^d`, then
`log J ≤ E (N_tr + 3P + 2(N + 1) + 2(N + 1)Q)`. -/
theorem q7b_log_card_le {d J Ntr E Kc Kl N : ℕ}
    (hJ : J ≤ (Ntr * (2 ^ ((2 * Kc + 1) ^ d)) ^ 3 * ((N + 1) * ((2 * Kl + 1) ^ d) ^ (N + 1)) ^ 2) ^ E) :
    Real.log J ≤ E * (Ntr + 3 * ((2 * Kc + 1 : ℕ) : ℝ) ^ d + 2 * ((N : ℝ) + 1) +
      2 * ((N : ℝ) + 1) * ((2 * Kl + 1 : ℕ) : ℝ) ^ d) := by
  set P : ℕ := (2 * Kc + 1) ^ d with hP
  set Q : ℕ := (2 * Kl + 1) ^ d with hQ
  set base : ℕ := Ntr * (2 ^ P) ^ 3 * ((N + 1) * Q ^ (N + 1)) ^ 2 with hbase
  have hRHS : 0 ≤ (E : ℝ) * (Ntr + 3 * ((2 * Kc + 1 : ℕ) : ℝ) ^ d + 2 * ((N : ℝ) + 1) +
      2 * ((N : ℝ) + 1) * ((2 * Kl + 1 : ℕ) : ℝ) ^ d) := by positivity
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · rw [hJ0, Nat.cast_zero, Real.log_zero]
    exact hRHS
  rcases Nat.eq_zero_or_pos E with hE0 | hE0
  · rw [hE0, pow_zero] at hJ
    have hJ1 : J = 1 := le_antisymm hJ hJ0
    rw [hJ1, Nat.cast_one, Real.log_one]
    exact hRHS
  have hbase0 : 0 < base := by
    by_contra h
    push Not at h
    have hb : base = 0 := Nat.le_zero.1 h
    rw [hb, zero_pow hE0.ne'] at hJ
    omega
  have hNtr : 0 < Ntr := by
    rcases Nat.eq_zero_or_pos Ntr with h | h
    · rw [hbase, h, zero_mul, zero_mul] at hbase0
      exact absurd hbase0 (lt_irrefl 0)
    · exact h
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hJle : (J : ℝ) ≤ (base : ℝ) ^ E := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ0
  have hlogJ : Real.log J ≤ E * Real.log base := by
    rw [← Real.log_pow]
    exact Real.log_le_log hJpos hJle
  have hlogbase : Real.log base ≤ Ntr + 3 * (P : ℝ) + 2 * ((N : ℝ) + 1) + 2 * ((N : ℝ) + 1) * Q := by
    have hNtrR : (0 : ℝ) < Ntr := by exact_mod_cast hNtr
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have e : (base : ℝ) = Ntr * ((2 : ℝ) ^ P) ^ 3 * (((N : ℝ) + 1) * (Q : ℝ) ^ (N + 1)) ^ 2 := by
      rw [hbase]
      push_cast
      ring
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h1 : Real.log Ntr ≤ Ntr := Real.log_le_self hNtrR.le
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have h3 : Real.log ((N : ℝ) + 1) ≤ (N : ℝ) + 1 := Real.log_le_self hN1.le
    have h4 : Real.log Q ≤ Q := Real.log_le_self hQR.le
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    have h5 : ((N + 1 : ℕ) : ℝ) * Real.log Q ≤ ((N : ℝ) + 1) * Q := by
      push_cast
      exact mul_le_mul_of_nonneg_left h4 hN1.le
    have h6 : (P : ℝ) * Real.log 2 ≤ P := by nlinarith
    push_cast at h5 ⊢
    nlinarith
  have hE : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  calc Real.log J ≤ E * Real.log base := hlogJ
    _ ≤ E * (Ntr + 3 * (P : ℝ) + 2 * ((N : ℝ) + 1) + 2 * ((N : ℝ) + 1) * Q) :=
        mul_le_mul_of_nonneg_left hlogbase hE
    _ = E * (Ntr + 3 * ((2 * Kc + 1 : ℕ) : ℝ) ^ d + 2 * ((N : ℝ) + 1) +
          2 * ((N : ℝ) + 1) * ((2 * Kl + 1 : ℕ) : ℝ) ^ d) := by
        rw [hP, hQ]
        push_cast
        ring

/-- `x^a ≤ x^b` for `1 ≤ x`, `a ≤ b`, and `A x^a ≤ A x^b` for `A ≥ 0`. -/
private theorem q7b_mul_rpow_le {A x a b : ℝ} (hA : 0 ≤ A) (hx : 1 ≤ x) (hab : a ≤ b) :
    A * x ^ a ≤ A * x ^ b :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hab) hA

/-- A natural cutoff `⌈B/μ⌉₊ + 2` with `μ ≥ c v^K` is at most `(B/c + 3) x^K`, `x = 1 + v⁻¹`. -/
private theorem q7b_cutoff_le {B μ c v K : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (hK : 0 ≤ K) (hv : 0 < v)
    (hμ : c * v ^ K ≤ μ) :
    ((⌈B / μ⌉₊ + 2 : ℕ) : ℝ) ≤ (B / c + 3) * (1 + 0 + v⁻¹) ^ K := by
  have hvK : 0 < v ^ K := Real.rpow_pos_of_pos hv K
  have hμ0 : 0 < μ := lt_of_lt_of_le (mul_pos hc hvK) hμ
  have hx : (1 : ℝ) ≤ 1 + 0 + v⁻¹ := by have := inv_pos.2 hv; linarith
  have hxK : 1 ≤ (1 + 0 + v⁻¹) ^ K := Real.one_le_rpow hx hK
  have hceil : (⌈B / μ⌉₊ : ℝ) < B / μ + 1 := Nat.ceil_lt_add_one (div_nonneg hB hμ0.le)
  have hinv : 1 / μ ≤ c⁻¹ * (1 + 0 + v⁻¹) ^ K := by
    have h1 : 1 / μ ≤ 1 / (c * v ^ K) := one_div_le_one_div_of_le (mul_pos hc hvK) hμ
    have h2 : 1 / (c * v ^ K) = c⁻¹ * v ^ (-K) := by
      rw [Real.rpow_neg hv.le]
      field_simp
    have h3 : v ^ (-K) ≤ (1 + 0 + v⁻¹) ^ K := by
      rw [Real.rpow_neg hv.le, ← Real.inv_rpow hv.le]
      exact Real.rpow_le_rpow (inv_pos.2 hv).le (by linarith) hK
    calc 1 / μ ≤ c⁻¹ * v ^ (-K) := h1.trans h2.le
      _ ≤ c⁻¹ * (1 + 0 + v⁻¹) ^ K := mul_le_mul_of_nonneg_left h3 (inv_pos.2 hc).le
  have hBμ : B / μ ≤ B / c * (1 + 0 + v⁻¹) ^ K := by
    calc B / μ = B * (1 / μ) := by ring
      _ ≤ B * (c⁻¹ * (1 + 0 + v⁻¹) ^ K) := mul_le_mul_of_nonneg_left hinv hB
      _ = B / c * (1 + 0 + v⁻¹) ^ K := by ring
  push_cast
  nlinarith

/-- **The catalogue bound as a polynomial in `v⁻¹`** (`b:lem-catalogue` with `b:lem-order`(d)). -/
theorem q7b_count_le_polyB {d E Ntr : ℕ} {L c Cmax K v μ ν : ℝ} {N : ℕ} (hL : 0 ≤ L) (hc : 0 < c)
    (hCmax : 0 ≤ Cmax) (hK : 0 ≤ K) (hv : 0 < v) (hμ : c * v ^ K ≤ μ) (hν : c * v ^ K ≤ ν)
    (hN : (N : ℝ) ≤ Cmax * v ^ (-K)) :
    (E : ℝ) * (Ntr + 3 * ((2 * (⌈L / μ⌉₊ + 2) + 1 : ℕ) : ℝ) ^ d + 2 * ((N : ℝ) + 1) +
      2 * ((N : ℝ) + 1) * ((2 * (⌈(5 / 2 : ℝ) / ν⌉₊ + 2) + 1 : ℕ) : ℝ) ^ d) ≤
      polyB (E * (Ntr + 3 * (2 * (L / c + 3) + 1) ^ d + 2 * (Cmax + 1) +
        2 * (Cmax + 1) * (2 * (5 / 2 / c + 3) + 1) ^ d)) (K * (d + 1)) 0 v⁻¹ := by
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = 1 + 0 + v⁻¹ := ⟨_, rfl⟩
  have hx : (1 : ℝ) ≤ x := by have := inv_pos.2 hv; rw [hxdef]; linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hxK : 1 ≤ x ^ K := Real.one_le_rpow hx hK
  have hxK0 : 0 ≤ x ^ K := by linarith
  -- the cell and lead cutoffs
  have hKc := q7b_cutoff_le hL hc hK hv hμ
  have hKl := q7b_cutoff_le (show (0 : ℝ) ≤ 5 / 2 by norm_num) hc hK hv hν
  rw [← hxdef] at hKc hKl
  have hcell : ((2 * (⌈L / μ⌉₊ + 2) + 1 : ℕ) : ℝ) ≤ (2 * (L / c + 3) + 1) * x ^ K := by
    have : ((2 * (⌈L / μ⌉₊ + 2) + 1 : ℕ) : ℝ) = 2 * ((⌈L / μ⌉₊ + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [this]
    nlinarith
  have hlead : ((2 * (⌈(5 / 2 : ℝ) / ν⌉₊ + 2) + 1 : ℕ) : ℝ) ≤ (2 * (5 / 2 / c + 3) + 1) * x ^ K := by
    have : ((2 * (⌈(5 / 2 : ℝ) / ν⌉₊ + 2) + 1 : ℕ) : ℝ) = 2 * ((⌈(5 / 2 : ℝ) / ν⌉₊ + 2 : ℕ) : ℝ) + 1 := by
      push_cast; ring
    rw [this]
    nlinarith
  have hpowd : ∀ {y A : ℝ}, 0 ≤ y → y ≤ A * x ^ K → y ^ d ≤ A ^ d * x ^ (K * d) := by
    intro y A hy hyA
    calc y ^ d ≤ (A * x ^ K) ^ d := pow_le_pow_left₀ hy hyA d
      _ = A ^ d * x ^ (K * d) := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ K), ← Real.rpow_mul hx0]
  have hP := hpowd (Nat.cast_nonneg _) hcell
  have hQ := hpowd (Nat.cast_nonneg _) hlead
  have hN1 : (N : ℝ) + 1 ≤ (Cmax + 1) * x ^ K := by
    have h1 : v ^ (-K) ≤ x ^ K := by
      rw [Real.rpow_neg hv.le, ← Real.inv_rpow hv.le]
      exact Real.rpow_le_rpow (inv_pos.2 hv).le (by rw [hxdef]; linarith) hK
    nlinarith [mul_le_mul_of_nonneg_left h1 hCmax]
  -- all terms at the common power `x^{K(d+1)}`
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = K * (d + 1) := ⟨_, rfl⟩
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdk : K * d ≤ k := by rw [hk]; nlinarith
  have hKk : K ≤ k := by rw [hk]; nlinarith
  have hsplit : x ^ K * x ^ (K * d) = x ^ k := by
    rw [← Real.rpow_add (by linarith), hk]
    ring_nf
  obtain ⟨Ap, hAp⟩ : ∃ Ap : ℝ, Ap = (2 * (L / c + 3) + 1) ^ d := ⟨_, rfl⟩
  obtain ⟨Aq, hAq⟩ : ∃ Aq : ℝ, Aq = (2 * (5 / 2 / c + 3) + 1) ^ d := ⟨_, rfl⟩
  rw [← hAp] at hP
  rw [← hAq] at hQ
  have hAp0 : 0 ≤ Ap := by rw [hAp]; positivity
  have hAq0 : 0 ≤ Aq := by rw [hAq]; positivity
  set P' : ℝ := ((2 * (⌈L / μ⌉₊ + 2) + 1 : ℕ) : ℝ) ^ d with hP'
  set Q' : ℝ := ((2 * (⌈(5 / 2 : ℝ) / ν⌉₊ + 2) + 1 : ℕ) : ℝ) ^ d with hQ'
  have hT1 : (Ntr : ℝ) ≤ Ntr * x ^ k :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow hx (by linarith))
  have hT2 : 3 * P' ≤ 3 * Ap * x ^ k := by
    have := q7b_mul_rpow_le hAp0 hx hdk
    linarith
  have hT3 : 2 * ((N : ℝ) + 1) ≤ 2 * (Cmax + 1) * x ^ k := by
    have := q7b_mul_rpow_le (show 0 ≤ 2 * (Cmax + 1) by linarith) hx hKk
    linarith
  have hT4 : 2 * ((N : ℝ) + 1) * Q' ≤ 2 * (Cmax + 1) * Aq * x ^ k := by
    have hq0 : (0 : ℝ) ≤ Q' := by rw [hQ']; positivity
    have hN0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    calc 2 * ((N : ℝ) + 1) * Q' ≤ 2 * ((Cmax + 1) * x ^ K) * (Aq * x ^ (K * d)) := by
          have h1 := mul_le_mul hN1 hQ hq0 (by positivity)
          linarith
      _ = 2 * (Cmax + 1) * Aq * (x ^ K * x ^ (K * d)) := by ring
      _ = 2 * (Cmax + 1) * Aq * x ^ k := by rw [hsplit]
  have hsum : (Ntr : ℝ) + 3 * P' + 2 * ((N : ℝ) + 1) + 2 * ((N : ℝ) + 1) * Q' ≤
      (Ntr + 3 * Ap + 2 * (Cmax + 1) + 2 * (Cmax + 1) * Aq) * x ^ k := by
    linarith
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hpoly : polyB (E * (Ntr + 3 * (2 * (L / c + 3) + 1) ^ d + 2 * (Cmax + 1) +
      2 * (Cmax + 1) * (2 * (5 / 2 / c + 3) + 1) ^ d)) (K * (d + 1)) 0 v⁻¹ =
      E * (Ntr + 3 * Ap + 2 * (Cmax + 1) + 2 * (Cmax + 1) * Aq) * x ^ k := by
    unfold polyB
    rw [← hxdef, ← hk, ← hAp, ← hAq]
  rw [hpoly]
  have h := mul_le_mul_of_nonneg_left hsum hE0
  linarith

end HigherDimLQGContinuity
