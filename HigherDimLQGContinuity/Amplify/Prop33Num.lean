import HigherDimLQGContinuity.Amplify.Recursion
import HigherDimLQGContinuity.Amplify.Lemma32Num

/-!
# The numerical bookkeeping of Proposition 3.3 (packet P7)

Blueprint `a:prop33`, "Constants" and "Estimates" (NA1 R9): the number of bands `N` (`p7Nb`), the geometric band
exponents `a_j = L^{-j}/4` (`p7a`), the lower bound `a_N ≥ c_a δ^{M₀}` (`p7a_N_ge`), the exponential estimates of
the recursion increments and of the final additive error (`p7_prop33_small`), and the elementary bound
`b e^x ≤ b + 2 b x` for the physical connector coefficient (`p7_exp_le_one_add_two_mul`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

/-! ## The number of bands -/

/-- The number of bands `N = ⌈log(4C₀/δ) / log(1/q_*)⌉`. -/
def p7Nb (C0 qs δ : ℝ) : ℕ := ⌈Real.log (4 * C0 / δ) / Real.log qs⁻¹⌉₊

theorem p7_log_inv_pos {qs : ℝ} (hqs : 0 < qs) (hqs1 : qs < 1) : 0 < Real.log qs⁻¹ :=
  Real.log_pos (one_lt_inv_iff₀.mpr ⟨hqs, hqs1⟩)

/-- `q_*^N C₀ ≤ δ/4` and `N ≤ (log(4C₀) + log δ⁻¹)/log(1/q_*) + 1`. -/
theorem p7Nb_spec {C0 qs δ : ℝ} (hC0 : 1 ≤ C0) (hqs : 0 < qs) (hqs1 : qs < 1) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    qs ^ p7Nb C0 qs δ * C0 ≤ δ / 4 ∧
      (p7Nb C0 qs δ : ℝ) ≤ (Real.log (4 * C0) + Real.log δ⁻¹) / Real.log qs⁻¹ + 1 := by
  set ℓq := Real.log qs⁻¹ with hℓq
  have hℓ : 0 < ℓq := p7_log_inv_pos hqs hqs1
  have h4C : 0 < 4 * C0 / δ := by positivity
  have hlog4C : Real.log (4 * C0 / δ) = Real.log (4 * C0) + Real.log δ⁻¹ := by
    rw [div_eq_mul_inv, Real.log_mul (by positivity) (by positivity)]
  have hlog0 : 0 ≤ Real.log (4 * C0 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  set N := p7Nb C0 qs δ with hN
  have hNge : Real.log (4 * C0 / δ) / ℓq ≤ N := Nat.le_ceil _
  have hNlt : (N : ℝ) < Real.log (4 * C0 / δ) / ℓq + 1 := Nat.ceil_lt_add_one (div_nonneg hlog0 hℓ.le)
  constructor
  · have hNℓ : Real.log (4 * C0 / δ) ≤ N * ℓq := by
      rwa [div_le_iff₀ hℓ] at hNge
    have hpow : qs ^ N = Real.exp (-(N * ℓq)) := by
      rw [hℓq, Real.log_inv, mul_neg, neg_neg, ← Real.exp_log (pow_pos hqs N), Real.log_pow]
    rw [hpow]
    have hexp : Real.exp (-(N * ℓq)) ≤ Real.exp (-Real.log (4 * C0 / δ)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hval : Real.exp (-Real.log (4 * C0 / δ)) = δ / (4 * C0) := by
      rw [Real.exp_neg, Real.exp_log h4C, inv_div]
    rw [hval] at hexp
    have hC0' : 0 < C0 := by linarith
    calc Real.exp (-(N * ℓq)) * C0 ≤ δ / (4 * C0) * C0 := mul_le_mul_of_nonneg_right hexp hC0'.le
      _ = δ / 4 := by field_simp
  · rw [← hlog4C]
    exact hNlt.le

/-! ## Band exponents -/

/-- The band exponents `a_j = L^{-j}/4`. -/
def p7a (L : ℝ) (j : ℕ) : ℝ := (L ^ j)⁻¹ / 4

theorem p7a_pos {L : ℝ} (hL : 0 < L) (j : ℕ) : 0 < p7a L j := by
  unfold p7a; positivity

theorem p7a_succ (L : ℝ) (j : ℕ) : p7a L (j + 1) = p7a L j / L := by
  unfold p7a
  rw [pow_succ, mul_inv]
  ring

theorem p7a_anti {L : ℝ} (hL : 1 ≤ L) : Antitone (p7a L) := by
  intro i j hij
  unfold p7a
  have hLpos : 0 < L := by linarith
  have : L ^ i ≤ L ^ j := pow_le_pow_right₀ hL hij
  have h2 : (L ^ j)⁻¹ ≤ (L ^ i)⁻¹ := inv_anti₀ (pow_pos hLpos i) this
  linarith

theorem p7a_le_quarter {L : ℝ} (hL : 1 ≤ L) (j : ℕ) : p7a L j ≤ 1 / 4 := by
  have := p7a_anti hL (Nat.zero_le j)
  simpa [p7a] using this

theorem p7a_one (L : ℝ) : p7a L 1 = 1 / (4 * L) := by
  unfold p7a; rw [pow_one]; field_simp

/-- `a_N ≥ δ^{M₀} / (4 L (4C₀)^{M₀})` for `N = p7Nb C₀ q_* δ`, `M₀ = log L / log(1/q_*)`. -/
theorem p7a_N_ge {C0 qs δ L : ℝ} (hC0 : 1 ≤ C0) (hqs : 0 < qs) (hqs1 : qs < 1) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hL : 1 ≤ L) :
    δ ^ (Real.log L / Real.log qs⁻¹) /
        (4 * L * (4 * C0) ^ (Real.log L / Real.log qs⁻¹)) ≤ p7a L (p7Nb C0 qs δ) := by
  set ℓq := Real.log qs⁻¹ with hℓq
  have hℓ : 0 < ℓq := p7_log_inv_pos hqs hqs1
  set M0 := Real.log L / ℓq with hM0
  have hLpos : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hM00 : 0 ≤ M0 := div_nonneg hlogL hℓ.le
  set N := p7Nb C0 qs δ with hN
  have h4C : 0 < 4 * C0 / δ := by positivity
  have hlog0 : 0 ≤ Real.log (4 * C0 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  have hNlt : (N : ℝ) < Real.log (4 * C0 / δ) / ℓq + 1 := Nat.ceil_lt_add_one (div_nonneg hlog0 hℓ.le)
  -- `L^N ≤ L (4C₀/δ)^{M₀}`
  have hLN : L ^ N ≤ L * (4 * C0 / δ) ^ M0 := by
    have h1 : L ^ N = Real.exp (N * Real.log L) := by
      rw [← Real.exp_log (pow_pos hLpos N), Real.log_pow]
    have h2 : (4 * C0 / δ) ^ M0 = Real.exp (Real.log (4 * C0 / δ) * M0) := Real.rpow_def_of_pos h4C M0
    rw [h1, h2]
    have h3 : (N : ℝ) * Real.log L ≤ Real.log L + Real.log (4 * C0 / δ) * M0 := by
      have : (N : ℝ) * Real.log L ≤ (Real.log (4 * C0 / δ) / ℓq + 1) * Real.log L :=
        mul_le_mul_of_nonneg_right hNlt.le hlogL
      have heq : (Real.log (4 * C0 / δ) / ℓq + 1) * Real.log L =
          Real.log L + Real.log (4 * C0 / δ) * M0 := by
        rw [hM0]; field_simp; ring
      linarith
    calc Real.exp (N * Real.log L) ≤ Real.exp (Real.log L + Real.log (4 * C0 / δ) * M0) :=
          Real.exp_le_exp.mpr h3
      _ = L * Real.exp (Real.log (4 * C0 / δ) * M0) := by rw [Real.exp_add, Real.exp_log hLpos]
  have hsplit : (4 * C0 / δ) ^ M0 = (4 * C0) ^ M0 / δ ^ M0 :=
    Real.div_rpow (by positivity) hδ.le M0
  have hδM : 0 < δ ^ M0 := Real.rpow_pos_of_pos hδ M0
  have h4CM : 0 < (4 * C0) ^ M0 := Real.rpow_pos_of_pos (by positivity) M0
  have hLNpos : 0 < L ^ N := pow_pos hLpos N
  unfold p7a
  rw [hsplit] at hLN
  rw [div_le_div_iff₀ (by positivity) (by norm_num), inv_mul_eq_div]
  rw [le_div_iff₀ hLNpos]
  calc δ ^ M0 * 4 * L ^ N ≤ δ ^ M0 * 4 * (L * ((4 * C0) ^ M0 / δ ^ M0)) := by gcongr
    _ = 4 * L * (4 * C0) ^ M0 := by field_simp

/-! ## The connector coefficient -/

/-- `e^x ≤ 1 + 2x` for `0 ≤ x ≤ 1`. -/
theorem p7_exp_le_one_add_two_mul {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg hx]; exact hx1)
  have h2 : Real.exp x - 1 - x ≤ x ^ 2 := (le_abs_self _).trans h
  have h3 : x ^ 2 ≤ x := by nlinarith
  linarith

/-! ## The smallness estimates -/

/-- `Λ ≤ e^Λ`. -/
theorem p7_le_exp_self (Λ : ℝ) : Λ ≤ Real.exp Λ := by
  have := Real.add_one_le_exp Λ
  linarith

/-- **The smallness estimates of Proposition 3.3** (abstract form). With `H = 2 e^{κ_H Λ + h' A}`,
`e₀ = e^{-c₀ n}`, `A = a_N n ≤ n/4`, `N ≤ K_N Λ`, `0 ≤ Γ ≤ K_Γ`, the recursion increments sum to at most `δ/4`
and the final additive error is at most `e`, as soon as `σA/2` and `c₀ n` dominate the displayed multiples of `Λ`. -/
theorem p7_prop33_small {σ β c₀ h h' κH Λ n A Γ e δ KN KΓ a1 H : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hc₀ : 0 < c₀) (hhσ : h ≤ σ / 32) (hhc : h ≤ c₀ / 32)
    (hh' : h' ≤ 3 / 2 * h) (hΛ1 : 1 ≤ Λ) (hδ : 0 < δ) (he : 0 < e)
    (hΛδ : Real.log δ⁻¹ ≤ Λ) (hΛe : Real.log e⁻¹ ≤ Λ) (hA0 : 0 ≤ A) (hAn : A ≤ n / 4)
    (hKN : 0 < KN) (hN : (N : ℝ) ≤ KN * Λ) (hΓ0 : 0 ≤ Γ) (hKΓ : 0 < KΓ) (hΓ : Γ ≤ KΓ)
    (ha1 : 2 * β * (a1 * n) ≤ c₀ / 16 * n)
    (hA1 : (|Real.log (128 * 4 ^ β * KN ^ 2 * KΓ)| + 2 * κH + 3) * Λ ≤ σ / 2 * A)
    (hA2 : (|Real.log (16 * KN * KΓ)| + κH + 2) * Λ ≤ σ / 2 * A)
    (hn1 : (|Real.log (16 * 4 ^ β * KN)| + κH + 2) * Λ ≤ 7 / 8 * c₀ * n)
    (hn2 : 2 * Λ ≤ c₀ * n) (hH : H = 2 * Real.exp (κH * Λ + h' * A)) :
    (N : ℝ) * (Real.exp (-(c₀ * n)) * H * 4 ^ β * Real.exp (2 * β * (a1 * n)) +
        N * (Γ * (4 * H) * H * 4 ^ β) * Real.exp (-(3 / 4 * σ * A))) ≤ δ / 4 ∧
      Real.exp (-(c₀ * n)) + N * (Γ * (4 * H) * Real.exp (-(σ * A))) ≤ e := by
  have hn0 : 0 ≤ n := by linarith
  have h4β : (0 : ℝ) < 4 ^ β := Real.rpow_pos_of_pos (by norm_num) _
  have hΛ0 : 0 ≤ Λ := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNexp : (N : ℝ) ≤ KN * Real.exp Λ := hN.trans (mul_le_mul_of_nonneg_left (p7_le_exp_self Λ) hKN.le)
  have hδ' := p7_exp_neg_le_of_log_inv_le hδ hΛδ
  have he' := p7_exp_neg_le_of_log_inv_le he hΛe
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  -- first term
  have hT1 : (N : ℝ) * (Real.exp (-(c₀ * n)) * H * 4 ^ β * Real.exp (2 * β * (a1 * n))) ≤ δ / 8 := by
    have hexp1 : Real.exp (-(c₀ * n)) * H * 4 ^ β * Real.exp (2 * β * (a1 * n)) ≤
        2 * 4 ^ β * Real.exp (κH * Λ - 7 / 8 * c₀ * n) := by
      have hh'A : h' * A ≤ c₀ / 16 * n := by
        have h1 : h' * A ≤ 3 / 2 * h * A := mul_le_mul_of_nonneg_right hh' hA0
        have h2 : 3 / 2 * h * A ≤ 3 / 2 * (c₀ / 32) * (n / 4) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hhc (by norm_num)) hAn hA0 (by positivity)
        linarith
      have heq : Real.exp (-(c₀ * n)) * H * 4 ^ β * Real.exp (2 * β * (a1 * n)) =
          2 * 4 ^ β * Real.exp (-(c₀ * n) + (κH * Λ + h' * A) + 2 * β * (a1 * n)) := by
        rw [hH]; simp only [Real.exp_add]; ring
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      linarith
    have hK : 0 < 16 * 4 ^ β * KN := by positivity
    have hlog : Real.log (16 * 4 ^ β * KN) + Λ ≤ 7 / 8 * c₀ * n - (κH + 1) * Λ := by
      have h1 := p7_le_abs_mul (a := Real.log (16 * 4 ^ β * KN)) hΛ1
      have h2 : (|Real.log (16 * 4 ^ β * KN)| + κH + 2) * Λ =
          |Real.log (16 * 4 ^ β * KN)| * Λ + κH * Λ + 2 * Λ := by ring
      have h3 : (κH + 1) * Λ = κH * Λ + Λ := by ring
      linarith
    have hmain := p7_mul_exp_le_exp hK hlog
    calc (N : ℝ) * (Real.exp (-(c₀ * n)) * H * 4 ^ β * Real.exp (2 * β * (a1 * n)))
        ≤ KN * Real.exp Λ * (2 * 4 ^ β * Real.exp (κH * Λ - 7 / 8 * c₀ * n)) :=
          mul_le_mul hNexp hexp1 (by positivity) (by positivity)
      _ = (16 * 4 ^ β * KN) * Real.exp (-(7 / 8 * c₀ * n - (κH + 1) * Λ)) / 8 := by
          have hx : Real.exp (-(7 / 8 * c₀ * n - (κH + 1) * Λ)) =
              Real.exp Λ * Real.exp (κH * Λ - 7 / 8 * c₀ * n) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hx]; ring
      _ ≤ Real.exp (-Λ) / 8 := by gcongr
      _ ≤ δ / 8 := by gcongr
  -- second term
  have hT2 : (N : ℝ) * (N * (Γ * (4 * H) * H * 4 ^ β) * Real.exp (-(3 / 4 * σ * A))) ≤ δ / 8 := by
    have hHH : Γ * (4 * H) * H * 4 ^ β = 16 * 4 ^ β * Γ * Real.exp (2 * (κH * Λ + h' * A)) := by
      have hsq : Real.exp (2 * (κH * Λ + h' * A)) =
          Real.exp (κH * Λ + h' * A) * Real.exp (κH * Λ + h' * A) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsq, hH]; ring
    have hexp2 : Real.exp (2 * (κH * Λ + h' * A)) * Real.exp (-(3 / 4 * σ * A)) ≤
        Real.exp (2 * κH * Λ - 1 / 2 * σ * A) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : h' * A ≤ 3 / 2 * (σ / 32) * A :=
        mul_le_mul_of_nonneg_right (hh'.trans (mul_le_mul_of_nonneg_left hhσ (by norm_num))) hA0
      have h2 : 0 ≤ σ * A := mul_nonneg hσ.le hA0
      have h3 : 3 / 2 * (σ / 32) * A = 3 / 64 * (σ * A) := by ring
      have h4 : 2 * (κH * Λ + h' * A) + -(3 / 4 * σ * A) = 2 * (κH * Λ) + 2 * (h' * A) - 3 / 4 * (σ * A) := by
        ring
      have h5 : 2 * κH * Λ - 1 / 2 * σ * A = 2 * (κH * Λ) - 1 / 2 * (σ * A) := by ring
      rw [h4, h5]
      linarith
    have hN2 : (N : ℝ) * N ≤ KN ^ 2 * Real.exp (2 * Λ) := by
      have := mul_le_mul hNexp hNexp hN0 (by positivity)
      calc (N : ℝ) * N ≤ KN * Real.exp Λ * (KN * Real.exp Λ) := this
        _ = KN ^ 2 * Real.exp (2 * Λ) := by
          rw [show (2 : ℝ) * Λ = Λ + Λ by ring, Real.exp_add]; ring
    have hK : 0 < 128 * 4 ^ β * KN ^ 2 * KΓ := by positivity
    have hlog : Real.log (128 * 4 ^ β * KN ^ 2 * KΓ) + Λ ≤ 1 / 2 * σ * A - (2 * κH + 2) * Λ := by
      have h1 := p7_le_abs_mul (a := Real.log (128 * 4 ^ β * KN ^ 2 * KΓ)) hΛ1
      have h2 : (|Real.log (128 * 4 ^ β * KN ^ 2 * KΓ)| + 2 * κH + 3) * Λ =
          |Real.log (128 * 4 ^ β * KN ^ 2 * KΓ)| * Λ + 2 * (κH * Λ) + 3 * Λ := by ring
      have h3 : (2 * κH + 2) * Λ = 2 * (κH * Λ) + 2 * Λ := by ring
      have h4 : σ / 2 * A = 1 / 2 * σ * A := by ring
      linarith
    have hmain := p7_mul_exp_le_exp hK hlog
    calc (N : ℝ) * (N * (Γ * (4 * H) * H * 4 ^ β) * Real.exp (-(3 / 4 * σ * A)))
        = (N * N) * (16 * 4 ^ β * Γ) *
            (Real.exp (2 * (κH * Λ + h' * A)) * Real.exp (-(3 / 4 * σ * A))) := by
          rw [hHH]; ring
      _ ≤ (KN ^ 2 * Real.exp (2 * Λ)) * (16 * 4 ^ β * KΓ) * Real.exp (2 * κH * Λ - 1 / 2 * σ * A) := by
          apply mul_le_mul _ hexp2 (by positivity) (by positivity)
          apply mul_le_mul hN2 _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hΓ (by positivity)
      _ = (128 * 4 ^ β * KN ^ 2 * KΓ) * Real.exp (-(1 / 2 * σ * A - (2 * κH + 2) * Λ)) / 8 := by
          have hx : Real.exp (-(1 / 2 * σ * A - (2 * κH + 2) * Λ)) =
              Real.exp (2 * Λ) * Real.exp (2 * κH * Λ - 1 / 2 * σ * A) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hx]; ring
      _ ≤ Real.exp (-Λ) / 8 := by gcongr
      _ ≤ δ / 8 := by gcongr
  -- the final additive error
  have hE1 : Real.exp (-(c₀ * n)) ≤ e / 2 := by
    have hK : (0 : ℝ) < 2 := by norm_num
    have hlog : Real.log 2 + Λ ≤ c₀ * n := by
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      linarith
    have hmain := p7_mul_exp_le_exp hK hlog
    linarith
  have hE2 : (N : ℝ) * (Γ * (4 * H) * Real.exp (-(σ * A))) ≤ e / 2 := by
    have hexp3 : (4 * H) * Real.exp (-(σ * A)) ≤ 8 * Real.exp (κH * Λ - 1 / 2 * σ * A) := by
      rw [hH, show 4 * (2 * Real.exp (κH * Λ + h' * A)) * Real.exp (-(σ * A)) =
        8 * (Real.exp (κH * Λ + h' * A) * Real.exp (-(σ * A))) by ring, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have h1 : h' * A ≤ 3 / 2 * (σ / 32) * A :=
        mul_le_mul_of_nonneg_right (hh'.trans (mul_le_mul_of_nonneg_left hhσ (by norm_num))) hA0
      have h2 : 0 ≤ σ * A := mul_nonneg hσ.le hA0
      have h3 : 3 / 2 * (σ / 32) * A = 3 / 64 * (σ * A) := by ring
      have h5 : κH * Λ - 1 / 2 * σ * A = κH * Λ - 1 / 2 * (σ * A) := by ring
      rw [h5]
      linarith
    have hK : 0 < 16 * KN * KΓ := by positivity
    have hlog : Real.log (16 * KN * KΓ) + Λ ≤ 1 / 2 * σ * A - (κH + 1) * Λ := by
      have h1 := p7_le_abs_mul (a := Real.log (16 * KN * KΓ)) hΛ1
      have h2 : (|Real.log (16 * KN * KΓ)| + κH + 2) * Λ =
          |Real.log (16 * KN * KΓ)| * Λ + κH * Λ + 2 * Λ := by ring
      have h3 : (κH + 1) * Λ = κH * Λ + Λ := by ring
      have h4 : σ / 2 * A = 1 / 2 * σ * A := by ring
      linarith
    have hmain := p7_mul_exp_le_exp hK hlog
    calc (N : ℝ) * (Γ * (4 * H) * Real.exp (-(σ * A)))
        = (N : ℝ) * Γ * ((4 * H) * Real.exp (-(σ * A))) := by ring
      _ ≤ (KN * Real.exp Λ) * KΓ * (8 * Real.exp (κH * Λ - 1 / 2 * σ * A)) := by
          apply mul_le_mul _ hexp3 (by positivity) (by positivity)
          exact mul_le_mul hNexp hΓ hΓ0 (by positivity)
      _ = (16 * KN * KΓ) * Real.exp (-(1 / 2 * σ * A - (κH + 1) * Λ)) / 2 := by
          have hx : Real.exp (-(1 / 2 * σ * A - (κH + 1) * Λ)) =
              Real.exp Λ * Real.exp (κH * Λ - 1 / 2 * σ * A) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hx]; ring
      _ ≤ Real.exp (-Λ) / 2 := by gcongr
      _ ≤ e / 2 := by gcongr
  constructor
  · have : (N : ℝ) * (Real.exp (-(c₀ * n)) * H * 4 ^ β * Real.exp (2 * β * (a1 * n)) +
        N * (Γ * (4 * H) * H * 4 ^ β) * Real.exp (-(3 / 4 * σ * A))) =
        (N : ℝ) * (Real.exp (-(c₀ * n)) * H * 4 ^ β * Real.exp (2 * β * (a1 * n))) +
          (N : ℝ) * (N * (Γ * (4 * H) * H * 4 ^ β) * Real.exp (-(3 / 4 * σ * A))) := by ring
    rw [this]
    linarith
  · linarith

/-! ## The depth condition and the failure probability -/

/-- From `n ≥ C₃ δ^{-M₃} Λ` (`δ ≤ 1`, `M₀ ≤ M₃`) and `a_N ≥ c_a δ^{M₀}`: `n ≥ C₃ Λ` and `a_N n ≥ c_a C₃ Λ`. -/
theorem p7_depth_lower {δ n Λ M0 M3 C3 ca aN : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : M0 ≤ M3)
    (hM3 : 0 ≤ M3) (hΛ : 0 ≤ Λ) (hC3 : 0 ≤ C3) (hca : 0 < ca) (haN : ca * δ ^ M0 ≤ aN)
    (hn : C3 * δ ^ (-M3) * Λ ≤ n) : C3 * Λ ≤ n ∧ ca * C3 * Λ ≤ aN * n := by
  have hδM3 : 1 ≤ δ ^ (-M3) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have h1 : C3 * Λ ≤ C3 * δ ^ (-M3) * Λ := by
    have : C3 * Λ * 1 ≤ C3 * Λ * δ ^ (-M3) := mul_le_mul_of_nonneg_left hδM3 (by positivity)
    linarith
  have hn0 : 0 ≤ n := le_trans (by positivity) hn
  refine ⟨h1.trans hn, ?_⟩
  have hprod : δ ^ M0 * δ ^ (-M3) = δ ^ (M0 - M3) := by
    rw [← Real.rpow_add hδ]; ring_nf
  have hge : 1 ≤ δ ^ (M0 - M3) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  calc ca * C3 * Λ ≤ ca * C3 * Λ * (δ ^ M0 * δ ^ (-M3)) := by
        rw [hprod]; exact le_mul_of_one_le_right (by positivity) hge
    _ = (ca * δ ^ M0) * (C3 * δ ^ (-M3) * Λ) := by ring
    _ ≤ aN * n := mul_le_mul haN hn (by positivity) (le_trans (by positivity) haN)

/-- **The failure probability of Proposition 3.3**, summed. Five failure terms, each decaying at least like
`e^{-c' a_N n}` (`a_N n ≤ n`), with `N ≤ K_N δ⁻¹`, `a_N ≥ c_a δ^{M₀}`, `R ≥ 1`, `0 < δ ≤ 1`: the sum is at most
`C₃ R^{M₃} δ^{-M₃} e^{-c₃ δ^{M₃} n}` for `C₃ ≥ K₁ + K₂ + K₃ + K₅ + K_N K₄`, `M₃ ≥ max(d, M₀, 1)`, `c₃ ≤ c' c_a`. -/
theorem p7_fail_sum (d : ℕ) {R δ n As aN M0 M3 C3 c3 ca cp KN K1 K2 K3 K4 K5 r1 r2 r3 r4 r5 : ℝ} {N : ℕ}
    (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hAs : As = aN * n) (hAsn : As ≤ n) (hn : 0 ≤ n)
    (haN : ca * δ ^ M0 ≤ aN) (hca : 0 < ca) (hcp : 0 < cp)
    (hr1 : cp ≤ r1) (hr2 : cp ≤ r2) (hr3 : cp ≤ r3) (hr4 : cp ≤ r4) (hr5 : cp ≤ r5)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hK4 : 0 ≤ K4) (hK5 : 0 ≤ K5) (hKN : 0 ≤ KN)
    (hN : (N : ℝ) ≤ KN * δ⁻¹) (hMd : (d : ℝ) ≤ M3) (hM03 : M0 ≤ M3) (hM1 : 1 ≤ M3)
    (hC3 : K1 + K2 + K3 + K5 + KN * K4 ≤ C3) (hc3 : c3 ≤ cp * ca) :
    K1 * Real.exp (-(r1 * As)) + K2 * Real.exp (-(r2 * As)) + K3 * Real.exp (-(r3 * n)) +
        N * (K4 * R ^ d * Real.exp (-(r4 * As))) + K5 * Real.exp (-(r5 * n)) ≤
      C3 * R ^ M3 * δ ^ (-M3) * Real.exp (-c3 * δ ^ M3 * n) := by
  have hAs0 : 0 ≤ As := by
    rw [hAs]; exact mul_nonneg (le_trans (by positivity) haN) hn
  set E := Real.exp (-(cp * As)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hexpA : ∀ r : ℝ, cp ≤ r → Real.exp (-(r * As)) ≤ E := fun r hr =>
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hr hAs0))
  have hexpn : ∀ r : ℝ, cp ≤ r → Real.exp (-(r * n)) ≤ E := fun r hr => by
    apply Real.exp_le_exp.mpr
    have h1 : cp * As ≤ cp * n := mul_le_mul_of_nonneg_left hAsn hcp.le
    have h2 : cp * n ≤ r * n := mul_le_mul_of_nonneg_right hr hn
    linarith
  have hRd : 1 ≤ R ^ d := one_le_pow₀ hR
  have hδinv : 1 ≤ δ⁻¹ := one_le_inv_iff₀.mpr ⟨hδ, hδ1⟩
  -- each term against `E`
  have hsum : K1 * Real.exp (-(r1 * As)) + K2 * Real.exp (-(r2 * As)) + K3 * Real.exp (-(r3 * n)) +
        N * (K4 * R ^ d * Real.exp (-(r4 * As))) + K5 * Real.exp (-(r5 * n)) ≤
      (K1 + K2 + K3 + K5 + KN * K4) * R ^ d * δ⁻¹ * E := by
    have h1 := mul_le_mul_of_nonneg_left (hexpA r1 hr1) hK1
    have h2 := mul_le_mul_of_nonneg_left (hexpA r2 hr2) hK2
    have h3 := mul_le_mul_of_nonneg_left (hexpn r3 hr3) hK3
    have h5 := mul_le_mul_of_nonneg_left (hexpn r5 hr5) hK5
    have h4 : (N : ℝ) * (K4 * R ^ d * Real.exp (-(r4 * As))) ≤ KN * δ⁻¹ * (K4 * R ^ d * E) := by
      apply mul_le_mul hN _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (hexpA r4 hr4) (by positivity)
    have hRδ : 1 ≤ R ^ d * δ⁻¹ := one_le_mul_of_one_le_of_one_le hRd hδinv
    have hK15 : (K1 + K2 + K3 + K5) * E ≤ (K1 + K2 + K3 + K5) * E * (R ^ d * δ⁻¹) :=
      le_mul_of_one_le_right (by positivity) hRδ
    have heq : (K1 + K2 + K3 + K5 + KN * K4) * R ^ d * δ⁻¹ * E =
        (K1 + K2 + K3 + K5) * E * (R ^ d * δ⁻¹) + KN * δ⁻¹ * (K4 * R ^ d * E) := by ring
    have hexp : (K1 + K2 + K3 + K5) * E = K1 * E + K2 * E + K3 * E + K5 * E := by ring
    rw [heq]
    linarith
  -- the final comparison
  have hRM : R ^ d ≤ R ^ M3 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hR hMd
  have hδM : δ⁻¹ ≤ δ ^ (-M3) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hEle : E ≤ Real.exp (-c3 * δ ^ M3 * n) := by
    apply Real.exp_le_exp.mpr
    have hδM3 : δ ^ M3 ≤ δ ^ M0 := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hM03
    have hδM30 : 0 ≤ δ ^ M3 := Real.rpow_nonneg hδ.le _
    have h1 : c3 * δ ^ M3 * n ≤ cp * ca * δ ^ M0 * n := by
      have := mul_le_mul hc3 hδM3 hδM30 (by positivity)
      exact mul_le_mul_of_nonneg_right this hn
    have h2 : cp * ca * δ ^ M0 * n ≤ cp * As := by
      rw [hAs]
      have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right haN hn) hcp.le
      calc cp * ca * δ ^ M0 * n = cp * (ca * δ ^ M0 * n) := by ring
        _ ≤ cp * (aN * n) := h3
    linarith
  have hC30 : 0 ≤ K1 + K2 + K3 + K5 + KN * K4 := by positivity
  have hC3' : 0 ≤ C3 := le_trans hC30 hC3
  have hR0 : 0 ≤ R := by linarith
  have hRd0 : 0 ≤ R ^ d := pow_nonneg hR0 d
  have hRM0 : 0 ≤ R ^ M3 := Real.rpow_nonneg hR0 _
  have hδM0 : 0 ≤ δ ^ (-M3) := Real.rpow_nonneg hδ.le _
  calc _ ≤ (K1 + K2 + K3 + K5 + KN * K4) * R ^ d * δ⁻¹ * E := hsum
    _ ≤ C3 * R ^ M3 * δ ^ (-M3) * Real.exp (-c3 * δ ^ M3 * n) := by
        apply mul_le_mul _ hEle hE0 (by positivity)
        apply mul_le_mul _ hδM (inv_nonneg.mpr hδ.le) (by positivity)
        exact mul_le_mul hC3 hRM hRd0 hC3'

end HigherDimLQGContinuity
