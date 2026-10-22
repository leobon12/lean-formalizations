import HigherDimLQGMetric.DGZ.BadBoxTools

/-!
# DGZ §5.2: real arithmetic for the bad-box probabilities (packet L4a2)

Source: [2] Lemmas 5.5–5.9 (TeX l. 2158–2389); planning audit MA7 D-OSC and D-5.5–5.9; blueprint
`r2:lem:oscconds`, `r2:lem:55`–`r2:lem:59`.

Elementary inequalities used to turn the union bounds into the exponential bounds of the lemmas:

* `BadBox.osc_arith` (D-OSC, condition (a′)): `j (9·2^{a_j})^d · 2e^{-(K√a_{j-1}/8 - C)²/C} ≤
  e^{-K a_j}` once `K` is large (`a_{j-1} ≥ K⁴`, `a_j ≤ 2a_{j-1}`, `j ≤ a_j`);
* `BadBox.exists_mul_two_exp_neg_sq_le`: `B · 2e^{-(x - C)²/C} ≤ η` for all large `x`;
* `BadBox.nine_le_exp_three`, `BadBox.two_le_exp_one`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGMetric

namespace DGZ

namespace BadBox

theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp 1
  linarith

theorem nine_le_exp_three : (9 : ℝ) ≤ Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [e]
  have h0 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
  calc (9 : ℝ) ≤ 2.7 ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := by gcongr

/-- `x ≤ e^x`. -/
theorem le_exp_self (x : ℝ) : x ≤ Real.exp x := by
  have := Real.add_one_le_exp x
  linarith

/-- `2^m ≤ e^m`. -/
theorem two_pow_le_exp (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp m := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) two_le_exp_one m

/-- **The arithmetic of condition (a′)** (MA7 D-OSC; blueprint `r2:lem:oscconds`(a)): for
`K ≥ 512C + 256C(3 + 5d) + 16C + 1`, `N ≥ K⁴`, `M ≤ 2N` and `J ≤ M`,
`J (9·2^M)^d · 2e^{-(K√N/8 - C)²/C} ≤ e^{-KM}`. -/
theorem osc_arith {C : ℝ} (hC : 0 < C) (d : ℕ) {K : ℝ}
    (hK : 512 * C + 256 * C * (3 + 5 * d) + 16 * C + 1 ≤ K) {N M J : ℕ}
    (hN : K ^ 4 ≤ N) (hM : (M : ℝ) ≤ 2 * N) (hJ : J ≤ M) :
    (J : ℝ) * ((9 : ℝ) * 2 ^ M) ^ d * (2 * Real.exp (-(K * √(N : ℝ) / 8 - C) ^ 2 / C)) ≤
      Real.exp (-(K * M)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hCd : 0 ≤ 256 * C * (3 + 5 * (d : ℝ)) := by positivity
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ hK1
  have hN1 : (1 : ℝ) ≤ N := hK4.trans hN
  -- `√N ≥ K²`
  have hsq : K ^ 2 ≤ √(N : ℝ) := by
    rw [Real.le_sqrt (by positivity) hN0]
    calc (K ^ 2) ^ 2 = K ^ 4 := by ring
      _ ≤ (N : ℝ) := hN
  have hsqN : √(N : ℝ) ^ 2 = N := Real.sq_sqrt hN0
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK1
  -- `x = K√N/8 ≥ 2C`
  have hx : 2 * C ≤ K * √(N : ℝ) / 8 := by
    have h1 : K ≤ K * √(N : ℝ) := by
      calc K = K * 1 := (mul_one K).symm
        _ ≤ K * √(N : ℝ) := mul_le_mul_of_nonneg_left (hK2.trans hsq) hK0.le
    linarith
  -- `(x - C)² ≥ K² N / 256`
  have hsq2 : K ^ 2 * N / 256 ≤ (K * √(N : ℝ) / 8 - C) ^ 2 := by
    have h1 : K * √(N : ℝ) / 16 ≤ K * √(N : ℝ) / 8 - C := by linarith
    have h2 : 0 ≤ K * √(N : ℝ) / 16 := by positivity
    calc K ^ 2 * N / 256 = (K * √(N : ℝ) / 16) ^ 2 := by
          rw [mul_div_assoc, div_pow, mul_pow, hsqN]
          ring
      _ ≤ (K * √(N : ℝ) / 8 - C) ^ 2 := pow_le_pow_left₀ h2 h1 2
  have hexp1 : Real.exp (-(K * √(N : ℝ) / 8 - C) ^ 2 / C) ≤
      Real.exp (-(K ^ 2 * N / (256 * C))) := by
    rw [Real.exp_le_exp, neg_div, neg_le_neg_iff, le_div_iff₀ hC]
    calc K ^ 2 * N / (256 * C) * C = K ^ 2 * N / 256 := by field_simp
      _ ≤ _ := hsq2
  -- the prefactors
  have hJe : (J : ℝ) ≤ Real.exp (2 * N) := by
    have : (J : ℝ) ≤ M := by exact_mod_cast hJ
    exact (this.trans hM).trans (le_exp_self _)
  have h9 : ((9 : ℝ) * 2 ^ M) ^ d ≤ Real.exp (3 * d + 2 * d * N) := by
    have h2M : (2 : ℝ) ^ M ≤ Real.exp (2 * N) :=
      (two_pow_le_exp M).trans (Real.exp_le_exp.2 hM)
    have hb : (9 : ℝ) * 2 ^ M ≤ Real.exp 3 * Real.exp (2 * N) :=
      mul_le_mul nine_le_exp_three h2M (by positivity) (Real.exp_pos _).le
    calc ((9 : ℝ) * 2 ^ M) ^ d ≤ (Real.exp 3 * Real.exp (2 * N)) ^ d :=
          pow_le_pow_left₀ (by positivity) hb d
      _ = Real.exp (3 * d + 2 * d * N) := by
          rw [← Real.exp_add, ← Real.exp_nat_mul]
          ring_nf
  -- `K² ≥ 256 C (2K + 3 + 5d)`
  have hKK : 256 * C * (2 * K + 3 + 5 * d) ≤ K ^ 2 := by
    have h1 : 512 * C + 256 * C * (3 + 5 * d) ≤ K := by linarith
    have h2 : 0 ≤ 256 * C * (3 + 5 * d) := by positivity
    nlinarith
  have hfin : 2 * (N : ℝ) + (3 * d + 2 * d * N) + 1 - K ^ 2 * N / (256 * C) ≤ -(K * M) := by
    have h1 : (2 * K + 3 + 5 * d) * N ≤ K ^ 2 * N / (256 * C) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : K * M ≤ K * (2 * N) := mul_le_mul_of_nonneg_left hM hK0.le
    nlinarith
  calc (J : ℝ) * ((9 : ℝ) * 2 ^ M) ^ d * (2 * Real.exp (-(K * √(N : ℝ) / 8 - C) ^ 2 / C))
      ≤ Real.exp (2 * N) * Real.exp (3 * d + 2 * d * N) *
          (Real.exp 1 * Real.exp (-(K ^ 2 * N / (256 * C)))) := by
        gcongr
        · exact two_le_exp_one
    _ = Real.exp (2 * N + (3 * d + 2 * d * N) + 1 - K ^ 2 * N / (256 * C)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(K * M)) := Real.exp_le_exp.2 hfin

/-- For `B ≥ 0`, `η > 0`, `C > 0`: `B · 2e^{-(x - C)²/C} ≤ η` for all `x ≥ x₀`. -/
theorem exists_mul_two_exp_neg_sq_le {C B η : ℝ} (hC : 0 < C) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → B * (2 * Real.exp (-(x - C) ^ 2 / C)) ≤ η := by
  set b := |Real.log ((2 * B + 1) / η)| with hb
  refine ⟨C + √(C * b), fun x hx => ?_⟩
  have hb0 : 0 ≤ b := abs_nonneg _
  have h1 : √(C * b) ≤ x - C := by linarith
  have h2 : C * b ≤ (x - C) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have h3 : Real.log ((2 * B + 1) / η) ≤ (x - C) ^ 2 / C := by
    rw [le_div_iff₀ hC]
    have := le_abs_self (Real.log ((2 * B + 1) / η))
    nlinarith
  have h4 : Real.exp (-(x - C) ^ 2 / C) ≤ η / (2 * B + 1) := by
    have hpos : 0 < (2 * B + 1) / η := by positivity
    calc Real.exp (-(x - C) ^ 2 / C) ≤ Real.exp (-Real.log ((2 * B + 1) / η)) := by
          rw [Real.exp_le_exp, neg_div]
          linarith
      _ = η / (2 * B + 1) := by
          rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  calc B * (2 * Real.exp (-(x - C) ^ 2 / C)) ≤ B * (2 * (η / (2 * B + 1))) := by gcongr
    _ ≤ η := by
        rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-! ## The arithmetic of Lemma 5.6 -/

/-- **Super-exponential terms** (Lemma 5.6, the across and certificate terms): for `C ≥ 0` and `b`
there is `N₀` with `C e^{-A log A} ≤ e^{-bN}/4` whenever `N₀ ≤ N ≤ A`. -/
theorem exists_mul_exp_neg_mul_log_le (C b : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N A : ℕ, N₀ ≤ N → N ≤ A →
      C * Real.exp (-(A : ℝ) * Real.log A) ≤ Real.exp (-(b * N)) / 4 := by
  set c := |b| + |Real.log (4 * C + 1)| with hc
  refine ⟨⌈Real.exp c⌉₊ + 1, fun N A hN hNA => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hNe : Real.exp c ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hN)
  have hlogN : c ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hNe
  have hA : (N : ℝ) ≤ A := by exact_mod_cast hNA
  have hlogA : Real.log N ≤ Real.log A := Real.log_le_log (by linarith) hA
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hNlog : (N : ℝ) * Real.log N ≤ A * Real.log A := mul_le_mul hA hlogA hlogN0 (by linarith)
  have hkey : b * N + Real.log (4 * C + 1) ≤ N * Real.log N := by
    have h1 : b ≤ |b| := le_abs_self b
    have h2 : Real.log (4 * C + 1) ≤ |Real.log (4 * C + 1)| := le_abs_self _
    have h3 : 0 ≤ |Real.log (4 * C + 1)| := abs_nonneg _
    have h4 : (N : ℝ) * c ≤ N * Real.log N := mul_le_mul_of_nonneg_left hlogN (by linarith)
    have h5 : b * N ≤ |b| * N := mul_le_mul_of_nonneg_right h1 (by linarith)
    have h6 : |Real.log (4 * C + 1)| ≤ |Real.log (4 * C + 1)| * N := by nlinarith
    rw [hc] at h4
    nlinarith
  have hpos : 0 < 4 * C + 1 := by linarith
  calc C * Real.exp (-(A : ℝ) * Real.log A) ≤ (4 * C + 1) / 4 * Real.exp (-(N * Real.log N)) := by
        have he : Real.exp (-(A : ℝ) * Real.log A) ≤ Real.exp (-(N * Real.log N)) := by
          rw [Real.exp_le_exp]
          linarith
        have hC' : C ≤ (4 * C + 1) / 4 := by linarith
        exact mul_le_mul hC' he (Real.exp_pos _).le (by positivity)
    _ = Real.exp (Real.log (4 * C + 1) - N * Real.log N) / 4 := by
        rw [Real.exp_sub, Real.exp_log hpos, Real.exp_neg]
        field_simp
    _ ≤ Real.exp (-(b * N)) / 4 := by
        gcongr
        linarith

/-- **The Gaussian supremum term** (Lemma 5.6): for `0 ≤ σ < τ`, `λ > 0`, `b ≥ 0` with
`σ² = 2λ (log 2) b`, there is `N₀` such that `2e^{-u²/(2 D log 2)} ≤ e^{-bN}/4` whenever `N ≥ N₀`,
`0 < D ≤ λN + 1` and `τN ≤ u`. -/
theorem exists_gauss_le {σ τ lam b : ℝ} (hσ : 0 ≤ σ) (hστ : σ < τ) (hlam : 0 < lam) (hb : 0 ≤ b)
    (hσb : σ ^ 2 = 2 * lam * Real.log 2 * b) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) (D u : ℝ), N₀ ≤ N → 0 < D → D ≤ lam * N + 1 → τ * N ≤ u →
      2 * Real.exp (-u ^ 2 / (2 * (D * Real.log 2))) ≤ Real.exp (-(b * N)) / 4 := by
  have hℓ : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  set γ := τ ^ 2 - σ ^ 2 with hγ
  have hγ0 : 0 < γ := by
    have : σ ^ 2 < τ ^ 2 := pow_lt_pow_left₀ hστ hσ two_ne_zero
    linarith
  set B := 2 * Real.log 2 * (lam * Real.log 8 + b) + 2 * Real.log 2 * Real.log 8 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨⌈B / γ⌉₊ + 1, fun N D u hN hD hDN hu => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hNB : B ≤ γ * N := by
    have h1 : B / γ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hN)
    rwa [div_le_iff₀ hγ0, mul_comm] at h1
  have hτ0 : 0 ≤ τ := hσ.trans hστ.le
  have hu0 : 0 ≤ u := (mul_nonneg hτ0 (by linarith)).trans hu
  have hu2 : τ ^ 2 * N ^ 2 ≤ u ^ 2 := by
    have := pow_le_pow_left₀ (mul_nonneg hτ0 (by linarith)) hu 2
    nlinarith
  -- `2 D ℓ (bN + log 8) ≤ u²`
  have hkey : 2 * (D * Real.log 2) * (b * N + Real.log 8) ≤ u ^ 2 := by
    have h1 : 2 * (D * Real.log 2) * (b * N + Real.log 8) ≤
        2 * ((lam * N + 1) * Real.log 2) * (b * N + Real.log 8) := by
      gcongr
    have h2 : 2 * ((lam * N + 1) * Real.log 2) * (b * N + Real.log 8) =
        σ ^ 2 * N ^ 2 + (2 * Real.log 2 * (lam * Real.log 8 + b)) * N +
          2 * Real.log 2 * Real.log 8 := by
      rw [hσb]
      ring
    have h3 : (2 * Real.log 2 * (lam * Real.log 8 + b)) * N + 2 * Real.log 2 * Real.log 8 ≤
        B * N := by
      rw [hB]
      have : 0 ≤ 2 * Real.log 2 * Real.log 8 := by positivity
      nlinarith
    have h4 : B * N ≤ γ * N * N := mul_le_mul_of_nonneg_right hNB (by linarith)
    have h5 : σ ^ 2 * N ^ 2 + γ * N * N = τ ^ 2 * N ^ 2 := by rw [hγ]; ring
    linarith
  have hexp : Real.exp (-u ^ 2 / (2 * (D * Real.log 2))) ≤ Real.exp (-(b * N + Real.log 8)) := by
    rw [Real.exp_le_exp, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    linarith
  calc 2 * Real.exp (-u ^ 2 / (2 * (D * Real.log 2))) ≤ 2 * Real.exp (-(b * N + Real.log 8)) := by
        gcongr
    _ = Real.exp (-(b * N)) / 4 := by
        rw [neg_add, Real.exp_add, Real.exp_neg (Real.log 8), Real.exp_log (by norm_num)]
        ring

/-- **The second Gaussian term** (Lemma 5.6): for `ε, C > 0` and any `b` there is `N₀` with
`2e^{-(εN)²/C} ≤ e^{-bN}/4` for `N ≥ N₀`. -/
theorem exists_two_exp_neg_sq_div_le {ε C : ℝ} (b : ℝ) (hε : 0 < ε) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 * Real.exp (-(ε * N) ^ 2 / C) ≤ Real.exp (-(b * N)) / 4 := by
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  refine ⟨⌈C * (b + Real.log 8) / ε ^ 2⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hNB : C * (b + Real.log 8) ≤ ε ^ 2 * N := by
    have h1 : C * (b + Real.log 8) / ε ^ 2 ≤ N :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hN)
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have hkey : C * (b * N + Real.log 8) ≤ (ε * N) ^ 2 := by
    have h0 : 0 ≤ C * Real.log 8 := by positivity
    have h1 : C * (b * N + Real.log 8) ≤ C * (b + Real.log 8) * N := by
      nlinarith [mul_le_mul_of_nonneg_left hN1 h0]
    have h2 : C * (b + Real.log 8) * N ≤ ε ^ 2 * N * N :=
      mul_le_mul_of_nonneg_right hNB (by linarith)
    nlinarith
  have hexp : Real.exp (-(ε * N) ^ 2 / C) ≤ Real.exp (-(b * N + Real.log 8)) := by
    rw [Real.exp_le_exp, neg_div, neg_le_neg_iff, le_div_iff₀ hC]
    linarith
  calc 2 * Real.exp (-(ε * N) ^ 2 / C) ≤ 2 * Real.exp (-(b * N + Real.log 8)) := by gcongr
    _ = Real.exp (-(b * N)) / 4 := by
        rw [neg_add, Real.exp_add, Real.exp_neg (Real.log 8), Real.exp_log (by norm_num)]
        ring

/-! ## Scale separation and powers of two -/

/-- For `λ > 0` and any `c` there is `K₀` with `c ≤ 2^{λK⁴}` for `K ≥ K₀` (the gap conditions
`c s_{i-1} ≤ s_i` of L4a1's `dgz_gap_of_le`). -/
theorem exists_le_two_rpow {lam : ℝ} (c : ℝ) (hlam : 0 < lam) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → c ≤ (2 : ℝ) ^ (lam * (K : ℝ) ^ 4) := by
  have hℓ : 0 < Real.log 2 := Real.log_pos one_lt_two
  set c' := max c 1 with hc'
  have hc'0 : 0 < c' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨⌈Real.log c' / (lam * Real.log 2)⌉₊ + 1, fun K hK => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by
    have : 1 ≤ K := by omega
    exact_mod_cast this
  have hKK : (K : ℝ) ≤ (K : ℝ) ^ 4 := by
    calc (K : ℝ) = K ^ 1 := (pow_one _).symm
      _ ≤ (K : ℝ) ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
  have hlog : Real.log c' / (lam * Real.log 2) ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hK)
  rw [div_le_iff₀ (by positivity)] at hlog
  calc c ≤ c' := le_max_left _ _
    _ = Real.exp (Real.log c') := (Real.exp_log hc'0).symm
    _ ≤ (2 : ℝ) ^ (lam * (K : ℝ) ^ 4) := by
        rw [Real.rpow_def_of_pos two_pos, Real.exp_le_exp]
        have := mul_le_mul_of_nonneg_left hKK (by positivity : 0 ≤ lam * Real.log 2)
        nlinarith

/-- `(2^x)^d = 2^{d x}`. -/
theorem two_rpow_pow (x : ℝ) (d : ℕ) : ((2 : ℝ) ^ x) ^ d = (2 : ℝ) ^ ((d : ℝ) * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]

/-! ## The arithmetic of Lemma 5.8 -/

/-- `C e^s ≤ e^t / 3` when `log(3C) + s ≤ t` (`C > 0`). -/
theorem mul_exp_le_exp_div_three {C s t : ℝ} (hC : 0 < C) (h : Real.log (3 * C) + s ≤ t) :
    C * Real.exp s ≤ Real.exp t / 3 := by
  rw [Real.log_mul (by norm_num) hC.ne'] at h
  have e1 : C * Real.exp s = Real.exp (Real.log C + s) := by
    rw [Real.exp_add, Real.exp_log hC]
  have e2 : Real.exp t / 3 = Real.exp (t - Real.log 3) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  rw [e1, e2, Real.exp_le_exp]
  linarith

/-- **The induction step of DGZ Lemma 5.8** (arithmetic): for `α > 0`, `λ > 0` with
`(2d + α)λ < α`, `β = d + 3α/2` and `C > 0` there is `K₀` such that for `K ≥ K₀`, `K⁴ ≤ N ≤ A` and
`A ≤ (1+λ)N + 1`:
`C (e^{-KA} + 2^{2dλN} (2^{-αN})² + 2^{(d-β)λN} 2^{-αN}) ≤ 2^{-αA}`. -/
theorem q_step_arith {α lam β C : ℝ} (d : ℕ) (hα : 0 < α) (hlam : 0 < lam)
    (hg : (2 * d + α) * lam < α) (hβ : β = d + 3 * α / 2) (hC : 0 < C) :
    ∃ K₀ : ℕ, ∀ K N A : ℕ, K₀ ≤ K → K ^ 4 ≤ N → N ≤ A → (A : ℝ) ≤ (1 + lam) * N + 1 →
      C * (Real.exp (-(K * A : ℝ)) + (2 : ℝ) ^ (2 * d * lam * N) * ((2 : ℝ) ^ (-(α * N))) ^ 2 +
        (2 : ℝ) ^ ((d - β) * lam * N) * (2 : ℝ) ^ (-(α * N))) ≤ (2 : ℝ) ^ (-(α * A)) := by
  have hℓ : 0 < Real.log 2 := Real.log_pos one_lt_two
  set ℓ := Real.log 2 with hℓdef
  set c := |Real.log (3 * C)| + α * ℓ with hc
  set g₁ := α - (2 * d + α) * lam with hg₁
  have hg₁0 : 0 < g₁ := by rw [hg₁]; linarith
  set g₂ := lam * α / 2 with hg₂
  have hg₂0 : 0 < g₂ := by positivity
  refine ⟨⌈α * ℓ + |Real.log (3 * C)| + 1⌉₊ + ⌈c / (ℓ * g₁)⌉₊ + ⌈c / (ℓ * g₂)⌉₊ + 1,
    fun K N A hK hN hNA hA => ?_⟩
  have hK1 : 1 ≤ K := by omega
  have hKN : K ≤ N := (Nat.le_self_pow (by norm_num) K).trans hN
  have hKr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hNr : (N : ℝ) ≤ A := by exact_mod_cast hNA
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hlog3 : Real.log (3 * C) ≤ |Real.log (3 * C)| := le_abs_self _
  have hc0 : 0 ≤ c := by positivity
  -- thresholds
  have hKa : α * ℓ + |Real.log (3 * C)| + 1 ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈α * ℓ + |Real.log (3 * C)| + 1⌉₊ ≤ K))
  have hK₁ : c / (ℓ * g₁) ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈c / (ℓ * g₁)⌉₊ ≤ K))
  have hK₂ : c / (ℓ * g₂) ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈c / (ℓ * g₂)⌉₊ ≤ K))
  have hN₁ : c ≤ ℓ * g₁ * N := by
    rw [div_le_iff₀ (by positivity)] at hK₁
    nlinarith
  have hN₂ : c ≤ ℓ * g₂ * N := by
    rw [div_le_iff₀ (by positivity)] at hK₂
    nlinarith
  have hαA : α * ℓ * A ≤ α * ℓ * ((1 + lam) * N + 1) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  -- the three terms
  have t1 : C * Real.exp (-(K * A : ℝ)) ≤ Real.exp (ℓ * (-(α * A))) / 3 := by
    refine mul_exp_le_exp_div_three hC ?_
    have habs := abs_nonneg (Real.log (3 * C))
    have h1 : (|Real.log (3 * C)| + 1) * 1 ≤ ((K : ℝ) - α * ℓ) * A := by
      have hA1 : (1 : ℝ) ≤ A := by
        have : (1 : ℝ) ≤ N := hK1r.trans hKr
        linarith
      exact mul_le_mul (by linarith) hA1 (by norm_num) (by linarith)
    nlinarith
  have t2 : C * ((2 : ℝ) ^ (2 * d * lam * N) * ((2 : ℝ) ^ (-(α * N))) ^ 2) ≤
      Real.exp (ℓ * (-(α * A))) / 3 := by
    have e : (2 : ℝ) ^ (2 * d * lam * N) * ((2 : ℝ) ^ (-(α * N))) ^ 2 =
        Real.exp (ℓ * (2 * d * lam * N) + 2 * (ℓ * (-(α * N)))) := by
      rw [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos two_pos, ← hℓdef,
        ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
    rw [e]
    refine mul_exp_le_exp_div_three hC ?_
    have h1 : ℓ * g₁ * N = ℓ * N * (α - (2 * d + α) * lam) := by rw [hg₁]; ring
    nlinarith
  have t3 : C * ((2 : ℝ) ^ ((d - β) * lam * N) * (2 : ℝ) ^ (-(α * N))) ≤
      Real.exp (ℓ * (-(α * A))) / 3 := by
    have e : (2 : ℝ) ^ ((d - β) * lam * N) * (2 : ℝ) ^ (-(α * N)) =
        Real.exp (ℓ * ((d - β) * lam * N) + ℓ * (-(α * N))) := by
      rw [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos two_pos, ← Real.exp_add]
    rw [e]
    refine mul_exp_le_exp_div_three hC ?_
    have h1 : ℓ * g₂ * N = ℓ * N * (lam * α / 2) := by rw [hg₂]; ring
    rw [hβ]
    nlinarith
  have hfin : (2 : ℝ) ^ (-(α * A)) = Real.exp (ℓ * (-(α * A))) := Real.rpow_def_of_pos two_pos _
  rw [hfin, mul_add, mul_add]
  linarith

end BadBox

end DGZ

end HigherDimLQGMetric
