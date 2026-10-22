import HigherDimLQGContinuity.Amplify.Prop33Consts

/-!
# The parameters of Proposition 3.3 and their numerics (packet P7)

Blueprint `a:prop33`, "Events" and "Estimates" (NA1 R9), for the constants `K : P7Consts33 …` of
`Amplify/Prop33Consts.lean`. Given `R, δ, e, n` with the depth condition `n ≥ C₃ δ^{-M₃} Λ`
(`Λ = 1 + log(1 + R) + log e⁻¹ + log δ⁻¹`), the parameters are the number of bands `N = p7Nb C₀ q_* δ`, the band
exponents `a_j = p7a L j`, `A = a_N n`, the escape factor `S = e^{w A}`, the confinement radius `W = S (R + 1)`, the
envelope threshold `H̄ = e^{κ_H Λ + h' A}`, `H = 2H̄`, the rough error `e₀ = e^{-c₀ n}`, the connector coefficient
`b' = b e^{2 C'_cap τ n}`, `Γ = b' + C₀ + 1` and the recursion increment `ε̄`.

* `p7_prop33_base`: the bracket, the number of bands and the depth consequences.
* `p7_prop33_num_det`: every numerical fact of the deterministic step (band radii, the hypotheses of Lemma 3.2 at
  radius `W + 2` with `e = q = e₀`, of the scale cap, the connector coefficient, and the final coefficient
  `b' + X_N ≤ b + δ`, error `e_N ≤ e`).
* `p7_prop33_num_fail`: the five failure probabilities and their sum
  `≤ C₃ R^{M₃} δ^{-M₃} e^{-c₃ δ^{M₃} n}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

variable {d : ℕ} {p σ β C₁ A pesc Cesc C0 C32 c32 Ccap Ccp ccp Cc Cb m M : ℝ}

/-- The bracket, the number of bands and the depth consequences. -/
theorem p7_prop33_base (hC0 : 1 ≤ C0) (K : P7Consts33 d p σ β C₁ A pesc Cesc C0 C32 c32 Ccap Ccp ccp Cc Cb m M)
    {R δ e n : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (he : 0 < e) (he1 : e ≤ 1)
    (hn : K.C₃ * δ ^ (-K.M₃) * p7Lam R e δ ≤ n) :
    1 ≤ p7Lam R e δ ∧ Real.log (1 + R) ≤ p7Lam R e δ ∧ Real.log e⁻¹ ≤ p7Lam R e δ ∧
      Real.log δ⁻¹ ≤ p7Lam R e δ ∧ K.qs ^ p7Nb C0 K.qs δ * C0 ≤ δ / 4 ∧
      (p7Nb C0 K.qs δ : ℝ) ≤ K.KN * p7Lam R e δ ∧ (p7Nb C0 K.qs δ : ℝ) ≤ K.KN * δ⁻¹ ∧
      K.ca * δ ^ K.M0 ≤ p7a K.L (p7Nb C0 K.qs δ) ∧ K.C₃ * p7Lam R e δ ≤ n ∧
      K.ca * K.C₃ * p7Lam R e δ ≤ p7a K.L (p7Nb C0 K.qs δ) * n ∧ 0 ≤ n := by
  obtain ⟨hΛ1, hΛR, hΛe, hΛδ⟩ := p7Lam_spec (le_trans zero_le_one hR) he he1 hδ hδ1
  set Λ := p7Lam R e δ with hΛdef
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨hqsN, hNle⟩ := p7Nb_spec hC0 K.hqs0 K.hqs1 hδ hδ1
  set N := p7Nb C0 K.qs δ with hNdef
  have hℓq : 0 < Real.log K.qs⁻¹ := p7_log_inv_pos K.hqs0 K.hqs1
  have hlog4C0 : 0 ≤ Real.log (4 * C0) := Real.log_nonneg (by linarith)
  have hNΛ : (N : ℝ) ≤ K.KN * Λ := by
    have h1 : Real.log (4 * C0) ≤ Real.log (4 * C0) * Λ := le_mul_of_one_le_right hlog4C0 hΛ1
    have h2 : (Real.log (4 * C0) + Real.log δ⁻¹) / Real.log K.qs⁻¹ ≤
        (Real.log (4 * C0) * Λ + Λ) / Real.log K.qs⁻¹ :=
      div_le_div_of_nonneg_right (by linarith only [h1, hΛδ]) hℓq.le
    calc (N : ℝ) ≤ (Real.log (4 * C0) + Real.log δ⁻¹) / Real.log K.qs⁻¹ + 1 := hNle
      _ ≤ (Real.log (4 * C0) * Λ + Λ) / Real.log K.qs⁻¹ + Λ := by linarith only [h2, hΛ1]
      _ = K.KN * Λ := by rw [K.hKN]; ring
  have hNδ : (N : ℝ) ≤ K.KN * δ⁻¹ := by
    have hδinv : 1 ≤ δ⁻¹ := one_le_inv_iff₀.mpr ⟨hδ, hδ1⟩
    have hlogδ : Real.log δ⁻¹ ≤ δ⁻¹ := by
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr hδ); linarith only [this]
    have h1 : Real.log (4 * C0) ≤ Real.log (4 * C0) * δ⁻¹ := le_mul_of_one_le_right hlog4C0 hδinv
    have h2 : (Real.log (4 * C0) + Real.log δ⁻¹) / Real.log K.qs⁻¹ ≤
        (Real.log (4 * C0) * δ⁻¹ + δ⁻¹) / Real.log K.qs⁻¹ :=
      div_le_div_of_nonneg_right (by linarith only [h1, hlogδ]) hℓq.le
    calc (N : ℝ) ≤ (Real.log (4 * C0) + Real.log δ⁻¹) / Real.log K.qs⁻¹ + 1 := hNle
      _ ≤ (Real.log (4 * C0) * δ⁻¹ + δ⁻¹) / Real.log K.qs⁻¹ + δ⁻¹ := by linarith only [h2, hδinv]
      _ = K.KN * δ⁻¹ := by rw [K.hKN]; ring
  have haN : K.ca * δ ^ K.M0 ≤ p7a K.L N := by
    have h := p7a_N_ge hC0 K.hqs0 K.hqs1 hδ hδ1 (L := K.L) (le_trans (by norm_num) K.hL5)
    rw [← K.hM0] at h
    calc K.ca * δ ^ K.M0 = δ ^ K.M0 / (4 * K.L * (4 * C0) ^ K.M0) := by rw [K.hca]; ring
      _ ≤ p7a K.L N := h
  obtain ⟨hnC, hAC⟩ := p7_depth_lower hδ hδ1 K.hM₃0' (le_trans zero_le_one K.hM₃1) hΛ0 K.hC₃0.le K.hca0
    haN hn
  have hn0 : 0 ≤ n := le_trans (mul_nonneg K.hC₃0.le hΛ0) hnC
  exact ⟨hΛ1, hΛR, hΛe, hΛδ, hqsN, hNΛ, hNδ, haN, hnC, hAC, hn0⟩

/-- **The deterministic numerics of Proposition 3.3.** -/
theorem p7_prop33_num_det (hd : 2 ≤ d) (hσ : 0 < σ) (hC0 : 1 ≤ C0)
    (hCb : 0 < Cb) (K : P7Consts33 d p σ β C₁ A pesc Cesc C0 C32 c32 Ccap Ccp ccp Cc Cb m M)
    {R δ e n τ b Λ : ℝ} {N : ℕ} (hR : 1 ≤ R) (hδ : 0 < δ) (hδ8 : δ < 1 / 8) (he : 0 < e)
    (hΛ1 : 1 ≤ Λ) (hΛR : Real.log (1 + R) ≤ Λ) (hΛe : Real.log e⁻¹ ≤ Λ) (hΛδ : Real.log δ⁻¹ ≤ Λ)
    (hqsN : K.qs ^ N * C0 ≤ δ / 4) (hNΛ : (N : ℝ) ≤ K.KN * Λ)
    (hnC : K.C₃ * Λ ≤ n) (hAC : K.ca * K.C₃ * Λ ≤ p7a K.L N * n) (hn0 : 0 ≤ n)
    (hτ0 : 0 ≤ τ) (hτ : τ * n ≤ K.c₃ * δ) (hb : 0 < b) (hbCb : b ≤ Cb)
    {As S W Hbar H e0 b' Γ εbar : ℝ}
    (hAs : As = p7a K.L N * n) (hS : S = Real.exp (K.w * As)) (hW : W = S * (R + 1))
    (hHbar : Hbar = Real.exp (K.κH * Λ + K.h' * As)) (hH : H = 2 * Hbar)
    (he0 : e0 = Real.exp (-(K.c₀ * n))) (hb' : b' = b * Real.exp (2 * K.Ccap' * τ * n))
    (hΓ : Γ = b' + C0 + 1)
    (hεbar : εbar = e0 * H * 4 ^ β * Real.exp (2 * β * (p7a K.L 1 * n)) +
      N * (Γ * (4 * H) * H * 4 ^ β) * Real.exp (-(3 / 4 * σ * (p7a K.L N * n)))) :
    4 ≤ S ∧ 1 ≤ Hbar ∧
      (∀ j < N, Real.log 4 ≤ p7a K.L (j + 1) * n ∧ 1 ≤ p7a K.L (j + 1) * n ∧
        2 * (p7a K.L (j + 1) * n) ≤ (⌈n⌉₊ : ℝ)) ∧
      0 < e0 ∧ e0 < 1 / 8 ∧
      C32 * (1 + Real.log (1 + (W + 2)) + Real.log e0⁻¹ + Real.log e0⁻¹) ≤ n ∧ τ * n ≤ c32 ∧
      1 ≤ ⌈n⌉₊ ∧ Real.log (1 + (W + 1)) ≤ 2 * (⌈n⌉₊ : ℝ) ∧
      (Real.sqrt (2 * d) + Ccap) * τ * (⌈n⌉₊ : ℝ) ≤ 2 * K.Ccap' * τ * n ∧
      0 ≤ b' ∧ b' ≤ b + δ / 4 ∧
      0 ≤ εbar ∧ b' + p7X K.qs C0 εbar N ≤ b + δ ∧ b' + C0 + N * εbar ≤ Γ ∧
      p7E e0 Γ H σ n (p7a K.L) N ≤ e := by
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ1
  have hδ1 : δ ≤ 1 := by linarith only [hδ8]
  have hL1 : 1 ≤ K.L := le_trans (by norm_num) K.hL5
  have hL0 : 0 < K.L := by linarith only [hL1]
  have ha0 : ∀ j, 0 ≤ p7a K.L j := fun j => (p7a_pos hL0 j).le
  have hanti := p7a_anti hL1
  have haq : ∀ j, p7a K.L j ≤ 1 / 4 := p7a_le_quarter hL1
  have hAs0 : 0 ≤ As := by rw [hAs]; exact mul_nonneg (ha0 N) hn0
  have hAsn : As ≤ n / 4 := by
    have := mul_le_mul_of_nonneg_right (haq N) hn0
    rw [hAs]; linarith only [this]
  have hAsC : K.ca * K.C₃ * Λ ≤ As := by rw [hAs]; exact hAC
  -- the depth consequences
  have hAw : 3 / K.w * Λ ≤ As := (mul_le_mul_of_nonneg_right K.hA1 hΛ0).trans hAsC
  have hA2 : 2 * Λ ≤ As := (mul_le_mul_of_nonneg_right K.hA2 hΛ0).trans hAsC
  have hA3 : 2 / σ * (|Real.log (128 * 4 ^ β * K.KN ^ 2 * K.KΓ)| + 2 * K.κH + 3) * Λ ≤ As :=
    (mul_le_mul_of_nonneg_right K.hA3 hΛ0).trans hAsC
  have hA4 : 2 / σ * (|Real.log (16 * K.KN * K.KΓ)| + K.κH + 2) * Λ ≤ As :=
    (mul_le_mul_of_nonneg_right K.hA4 hΛ0).trans hAsC
  have hn32 : 8 * C32 * Λ ≤ n := (mul_le_mul_of_nonneg_right K.hn1 hΛ0).trans hnC
  have hn8c : 8 / K.c₀ * Λ ≤ n := (mul_le_mul_of_nonneg_right K.hn2 hΛ0).trans hnC
  have hn3 : 3 * Λ ≤ n := (mul_le_mul_of_nonneg_right K.hn3 hΛ0).trans hnC
  have hn7c : 8 / (7 * K.c₀) * (|Real.log (16 * 4 ^ β * K.KN)| + K.κH + 2) * Λ ≤ n :=
    (mul_le_mul_of_nonneg_right K.hn4 hΛ0).trans hnC
  have hn2c : 2 / K.c₀ * Λ ≤ n := (mul_le_mul_of_nonneg_right K.hn5 hΛ0).trans hnC
  have hc₀ := K.hc₀
  have hw0 := K.hw0
  have hn1 : 3 ≤ n := by linarith only [hn3, hΛ1]
  -- `S ≥ 4` and `H̄ ≥ 1`
  have hwAs : 3 * Λ ≤ K.w * As := by
    have h1 : K.w * (3 / K.w * Λ) ≤ K.w * As := mul_le_mul_of_nonneg_left hAw hw0.le
    have h2 : K.w * (3 / K.w * Λ) = 3 * Λ := by field_simp
    linarith only [h1, h2]
  have hS4 : 4 ≤ S := by
    rw [hS]
    have := Real.add_one_le_exp (K.w * As)
    linarith only [this, hwAs, hΛ1]
  have hHbar1 : 1 ≤ Hbar := by
    rw [hHbar]
    apply Real.one_le_exp
    exact add_nonneg (mul_nonneg K.hκH0 hΛ0) (mul_nonneg K.hh'0 hAs0)
  -- the bands
  have hbands : ∀ j < N, Real.log 4 ≤ p7a K.L (j + 1) * n ∧ 1 ≤ p7a K.L (j + 1) * n ∧
      2 * (p7a K.L (j + 1) * n) ≤ (⌈n⌉₊ : ℝ) := by
    intro j hj
    have h1 : As ≤ p7a K.L (j + 1) * n := by
      rw [hAs]; exact mul_le_mul_of_nonneg_right (hanti (by omega : j + 1 ≤ N)) hn0
    have h2 : p7a K.L (j + 1) * n ≤ n / 4 := by
      have := mul_le_mul_of_nonneg_right (haq (j + 1)) hn0
      linarith only [this]
    have h4 := p7_log_four_le
    have hN : n ≤ (⌈n⌉₊ : ℝ) := Nat.le_ceil n
    refine ⟨by linarith only [h1, hA2, hΛ1, h4], by linarith only [h1, hA2, hΛ1],
      by linarith only [h2, hN, hn0]⟩
  -- the rough comparison at radius `W + 2`
  have he00 : 0 < e0 := by rw [he0]; exact Real.exp_pos _
  have hc₀n : 8 ≤ K.c₀ * n := by
    have h1 : K.c₀ * (8 / K.c₀ * Λ) ≤ K.c₀ * n := mul_le_mul_of_nonneg_left hn8c hc₀.le
    have h2 : K.c₀ * (8 / K.c₀ * Λ) = 8 * Λ := by field_simp
    linarith only [h1, h2, hΛ1]
  have he08 : e0 < 1 / 8 := by
    rw [he0]
    have h8 := p7_log_eight_le
    have h1 : Real.exp (-(K.c₀ * n)) < Real.exp (-Real.log 8) :=
      Real.exp_lt_exp.mpr (by linarith only [h8, hc₀n])
    have h2 : Real.exp (-Real.log 8) = 1 / 8 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    linarith only [h1, h2]
  have hloge0 : Real.log e0⁻¹ = K.c₀ * n := by rw [he0, Real.log_inv, Real.log_exp, neg_neg]
  have hR1 : R + 1 ≤ Real.exp Λ := by
    have := p7_le_exp_of_log_le (by linarith only [hR]) hΛR
    linarith only [this]
  have hS0 : 0 < S := by rw [hS]; exact Real.exp_pos _
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hWexp : W ≤ Real.exp (K.w * As + Λ) := by
    rw [hW, hS, Real.exp_add]
    exact mul_le_mul_of_nonneg_left hR1 (Real.exp_pos _).le
  have hE1 : 1 ≤ Real.exp (K.w * As + Λ) := Real.one_le_exp (by positivity)
  have hlogW : Real.log (1 + (W + 2)) ≤ 2 + (K.w * As + Λ) := by
    have h3W : 1 + (W + 2) ≤ 4 * Real.exp (K.w * As + Λ) := by linarith only [hWexp, hE1]
    calc Real.log (1 + (W + 2)) ≤ Real.log (4 * Real.exp (K.w * As + Λ)) :=
          Real.log_le_log (by linarith only [hW0]) h3W
      _ = Real.log 4 + (K.w * As + Λ) := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ 2 + (K.w * As + Λ) := by linarith only [p7_log_four_le]
  have hC32w : C32 * K.w ≤ 1 / 4 := by linarith only [K.hwC]
  have hC320 : 0 < C32 := by
    have := K.hc₀C
    by_contra hneg
    push Not at hneg
    have : 8 * C32 * K.c₀ ≤ 0 := by
      have h1 : 8 * C32 ≤ 0 := by linarith only [hneg]
      exact mul_nonpos_of_nonpos_of_nonneg h1 hc₀.le
    linarith only [this, K.hc₀C]
  have hdepth32 : C32 * (1 + Real.log (1 + (W + 2)) + Real.log e0⁻¹ + Real.log e0⁻¹) ≤ n := by
    rw [hloge0]
    have h1 : C32 * Real.log (1 + (W + 2)) ≤ C32 * (2 + (K.w * As + Λ)) :=
      mul_le_mul_of_nonneg_left hlogW hC320.le
    have h2 : C32 * (K.w * As) ≤ 1 / 4 * As := by
      have := mul_le_mul_of_nonneg_right hC32w hAs0
      linarith only [this]
    have h3 : C32 * (2 * (K.c₀ * n)) = n / 4 := by
      have := K.hc₀C
      linear_combination (n / 4) * this
    have h4 : C32 * (1 + Real.log (1 + (W + 2)) + K.c₀ * n + K.c₀ * n) =
        C32 + C32 * Real.log (1 + (W + 2)) + C32 * (2 * (K.c₀ * n)) := by ring
    have h5 : C32 * (2 + (K.w * As + Λ)) = 2 * C32 + C32 * (K.w * As) + C32 * Λ := by ring
    have h6 : 4 * (C32 * Λ) ≤ n / 2 := by linarith only [hn32]
    have h7 : C32 ≤ C32 * Λ := le_mul_of_one_le_right hC320.le hΛ1
    linarith only [h1, h2, h3, h4, h5, h6, h7, hAsn, hn0]
  have hτ32 : τ * n ≤ c32 := by
    have h1 : K.c₃ * δ ≤ K.c₃ := mul_le_of_le_one_right K.hc₃0.le hδ1
    linarith only [hτ, h1, K.hc₃2]
  -- the cap
  have hN : n ≤ (⌈n⌉₊ : ℝ) := Nat.le_ceil n
  have hN1 : 1 ≤ ⌈n⌉₊ := by
    have h1 : (1 : ℝ) ≤ (⌈n⌉₊ : ℝ) := by linarith only [hN, hn1]
    exact_mod_cast h1
  have hwhalf : K.w ≤ 1 / 2 := by
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 := mul_le_mul_of_nonneg_right hd2 hw0.le
    linarith only [h1, K.hwd]
  have hlogW1 : Real.log (1 + (W + 1)) ≤ 2 * (⌈n⌉₊ : ℝ) := by
    have h1 : Real.log (1 + (W + 1)) ≤ Real.log (1 + (W + 2)) :=
      Real.log_le_log (by linarith only [hW0]) (by linarith only)
    have h2 : K.w * As ≤ n / 8 := by
      have := mul_le_mul hwhalf hAsn hAs0 (by norm_num)
      linarith only [this]
    linarith only [h1, hlogW, h2, hn3, hΛ1, hN]
  have hcapτ : (Real.sqrt (2 * d) + Ccap) * τ * (⌈n⌉₊ : ℝ) ≤ 2 * K.Ccap' * τ * n := by
    rw [← K.hCcap']
    have hNle : (⌈n⌉₊ : ℝ) ≤ 2 * n := by
      have := Nat.ceil_lt_add_one hn0
      linarith only [this, hn1]
    have := mul_le_mul_of_nonneg_left hNle (mul_nonneg K.hCcap'0.le hτ0)
    linarith only [this]
  -- the connector coefficient
  have hx0 : 0 ≤ 2 * K.Ccap' * τ * n := by
    have := K.hCcap'0
    positivity
  have hx1 : 2 * K.Ccap' * τ * n ≤ δ := by
    have h1 : 2 * K.Ccap' * τ * n = 2 * K.Ccap' * (τ * n) := by ring
    have h2 : 2 * K.Ccap' * (τ * n) ≤ 2 * K.Ccap' * (K.c₃ * δ) :=
      mul_le_mul_of_nonneg_left hτ (by linarith only [K.hCcap'0])
    have h3 : 2 * K.Ccap' * (K.c₃ * δ) = (2 * K.Ccap' * K.c₃) * δ := by ring
    have h4 : (2 * K.Ccap' * K.c₃) * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right K.hc₃4 hδ.le
    linarith only [h1, h2, h3, h4]
  have hb'0 : 0 ≤ b' := by rw [hb']; positivity
  have hb'le : b' ≤ b + δ / 4 := by
    have hexp := p7_exp_le_one_add_two_mul hx0 (by linarith only [hx1, hδ1])
    have h1 : b' ≤ b * (1 + 2 * (2 * K.Ccap' * τ * n)) := by
      rw [hb']; exact mul_le_mul_of_nonneg_left hexp hb.le
    have h2 : b * (2 * (2 * K.Ccap' * τ * n)) ≤ Cb * (4 * K.Ccap' * (K.c₃ * δ)) := by
      apply mul_le_mul hbCb _ (by positivity) hCb.le
      have := mul_le_mul_of_nonneg_left hτ (by linarith only [K.hCcap'0] : (0 : ℝ) ≤ 4 * K.Ccap')
      linarith only [this]
    have h3 : Cb * (4 * K.Ccap' * (K.c₃ * δ)) = (16 * Cb * K.Ccap' * K.c₃) * δ / 4 := by ring
    have h4 : (16 * Cb * K.Ccap' * K.c₃) * δ / 4 ≤ 1 * δ / 4 := by
      have := mul_le_mul_of_nonneg_right K.hc₃3 hδ.le
      linarith only [this]
    have h5 : b * (1 + 2 * (2 * K.Ccap' * τ * n)) = b + b * (2 * (2 * K.Ccap' * τ * n)) := by ring
    linarith only [h1, h2, h3, h4, h5]
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; linarith only [hb'0, hC0]
  have hΓK : Γ ≤ K.KΓ := by
    rw [hΓ, K.hKΓ]; linarith only [hb'le, hbCb, hδ1]
  -- the smallness estimates
  have hH0 : 0 ≤ H := by rw [hH]; linarith only [hHbar1]
  have ha1 : 2 * β * (p7a K.L 1 * n) ≤ K.c₀ / 16 * n := by
    rw [p7a_one]
    have h1 : 2 * β * (1 / (4 * K.L)) ≤ K.c₀ / 16 := by
      rw [show 2 * β * (1 / (4 * K.L)) = β / (2 * K.L) by field_simp; ring, div_le_iff₀ (by positivity)]
      linarith only [K.hLc]
    have := mul_le_mul_of_nonneg_right h1 hn0
    linarith only [this]
  have hsA1 : (|Real.log (128 * 4 ^ β * K.KN ^ 2 * K.KΓ)| + 2 * K.κH + 3) * Λ ≤ σ / 2 * As := by
    have h1 := mul_le_mul_of_nonneg_left hA3 (by linarith only [hσ] : (0 : ℝ) ≤ σ / 2)
    have h2 : σ / 2 * (2 / σ * (|Real.log (128 * 4 ^ β * K.KN ^ 2 * K.KΓ)| + 2 * K.κH + 3) * Λ) =
        (|Real.log (128 * 4 ^ β * K.KN ^ 2 * K.KΓ)| + 2 * K.κH + 3) * Λ := by field_simp
    linarith only [h1, h2]
  have hsA2 : (|Real.log (16 * K.KN * K.KΓ)| + K.κH + 2) * Λ ≤ σ / 2 * As := by
    have h1 := mul_le_mul_of_nonneg_left hA4 (by linarith only [hσ] : (0 : ℝ) ≤ σ / 2)
    have h2 : σ / 2 * (2 / σ * (|Real.log (16 * K.KN * K.KΓ)| + K.κH + 2) * Λ) =
        (|Real.log (16 * K.KN * K.KΓ)| + K.κH + 2) * Λ := by field_simp
    linarith only [h1, h2]
  have hsn1 : (|Real.log (16 * 4 ^ β * K.KN)| + K.κH + 2) * Λ ≤ 7 / 8 * K.c₀ * n := by
    have h1 := mul_le_mul_of_nonneg_left hn7c (by positivity : (0 : ℝ) ≤ 7 / 8 * K.c₀)
    have h2 : 7 / 8 * K.c₀ * (8 / (7 * K.c₀) * (|Real.log (16 * 4 ^ β * K.KN)| + K.κH + 2) * Λ) =
        (|Real.log (16 * 4 ^ β * K.KN)| + K.κH + 2) * Λ := by field_simp
    linarith only [h1, h2]
  have hsn2 : 2 * Λ ≤ K.c₀ * n := by
    have h1 := mul_le_mul_of_nonneg_left hn2c hc₀.le
    have h2 : K.c₀ * (2 / K.c₀ * Λ) = 2 * Λ := by field_simp
    linarith only [h1, h2]
  have hHdef' : H = 2 * Real.exp (K.κH * Λ + K.h' * As) := by rw [hH, hHbar]
  obtain ⟨hsmall1, hsmall2⟩ := p7_prop33_small (N := N) (Γ := Γ) (a1 := p7a K.L 1) hσ hc₀ K.hhσ K.hhc
    K.hh' hΛ1 hδ he hΛδ hΛe hAs0 hAsn K.hKN0 hNΛ hΓ0 K.hKΓ0 hΓK ha1 hsA1 hsA2 hsn1 hsn2 hHdef'
  have hNε : (N : ℝ) * εbar ≤ δ / 4 := by
    rw [hεbar, he0, hAs] at *
    exact hsmall1
  have hεbar0 : 0 ≤ εbar := by
    rw [hεbar]
    have h4β : (0 : ℝ) < 4 ^ β := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hEN : p7E e0 Γ H σ n (p7a K.L) N ≤ e := by
    unfold p7E
    rw [he0]
    rw [hAs] at hsmall2
    exact hsmall2
  have hXN : b' + p7X K.qs C0 εbar N ≤ b + δ := by
    unfold p7X
    linarith only [hb'le, hqsN, hNε, hδ]
  have hΓε : b' + C0 + N * εbar ≤ Γ := by
    rw [hΓ]; linarith only [hNε, hδ1]
  exact ⟨hS4, hHbar1, hbands, he00, he08, hdepth32, hτ32, hN1, hlogW1, hcapτ, hb'0, hb'le, hεbar0,
    hXN, hΓε, hEN⟩

/-- **The failure numerics of Proposition 3.3.** -/
theorem p7_prop33_num_fail (hC₁ : 0 < C₁) (hA : 0 ≤ A) (hCc : 0 < Cc) (hCcp : 0 < Ccp)
    (hccp : 0 < ccp)
    (K : P7Consts33 d p σ β C₁ A pesc Cesc C0 C32 c32 Ccap Ccp ccp Cc Cb m M)
    {R δ n Λ : ℝ} {N : ℕ} (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hΛ1 : 1 ≤ Λ) (hΛR : Real.log (1 + R) ≤ Λ)
    (hNδ : (N : ℝ) ≤ K.KN * δ⁻¹) (haN : K.ca * δ ^ K.M0 ≤ p7a K.L N) (hn0 : 0 ≤ n)
    {As S W Hbar : ℝ} (hAs : As = p7a K.L N * n) (hS : S = Real.exp (K.w * As))
    (hW : W = S * (R + 1)) (hHbar : Hbar = Real.exp (K.κH * Λ + K.h' * As)) :
    Cesc * S ^ (-pesc) ≤ K.Cesc' * Real.exp (-(pesc * K.w * As)) ∧
      C₁ * (1 + (W + 1)) ^ A / Hbar ^ p ≤ 1 * Real.exp (-(p * K.h * As)) ∧
      (∀ j < N, Cc * (1 + W) ^ d * Real.exp (-2 * (p7a K.L (j + 1) * n)) ≤
        Cc * 4 ^ d * R ^ d * Real.exp (-(1 * As))) ∧
      Ccp * Real.exp (-ccp * (⌈n⌉₊ : ℝ)) ≤ Ccp * Real.exp (-(ccp * n)) ∧
      K.Cesc' * Real.exp (-(pesc * K.w * As)) + 1 * Real.exp (-(p * K.h * As)) +
          1 * Real.exp (-(K.c₀ * n)) + N * (Cc * 4 ^ d * R ^ d * Real.exp (-(1 * As))) +
          Ccp * Real.exp (-(ccp * n)) ≤
        K.C₃ * R ^ K.M₃ * δ ^ (-K.M₃) * Real.exp (-K.c₃ * δ ^ K.M₃ * n) := by
  have hL1 : 1 ≤ K.L := le_trans (by norm_num) K.hL5
  have hL0 : 0 < K.L := by linarith only [hL1]
  have ha0 : ∀ j, 0 ≤ p7a K.L j := fun j => (p7a_pos hL0 j).le
  have hanti := p7a_anti hL1
  have haq : ∀ j, p7a K.L j ≤ 1 / 4 := p7a_le_quarter hL1
  have hAs0 : 0 ≤ As := by rw [hAs]; exact mul_nonneg (ha0 N) hn0
  have hAsn : As ≤ n := by
    have := mul_le_mul_of_nonneg_right (haq N) hn0
    rw [hAs]; linarith only [this, hn0]
  have hw0 := K.hw0
  have hS1 : 1 ≤ S := by rw [hS]; exact Real.one_le_exp (mul_nonneg hw0.le hAs0)
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hR1 : R + 1 ≤ Real.exp Λ := by
    have := p7_le_exp_of_log_le (by linarith only [hR]) hΛR
    linarith only [this]
  -- escape
  have hesc : Cesc * S ^ (-pesc) ≤ K.Cesc' * Real.exp (-(pesc * K.w * As)) := by
    have hpow : S ^ (-pesc) = Real.exp (-(pesc * K.w * As)) := by
      rw [hS, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1; ring
    rw [hpow]
    exact mul_le_mul_of_nonneg_right K.hCesc' (Real.exp_pos _).le
  -- envelope
  have henv : C₁ * (1 + (W + 1)) ^ A / Hbar ^ p ≤ 1 * Real.exp (-(p * K.h * As)) := by
    have hWexp : W ≤ Real.exp (K.w * As + Λ) := by
      rw [hW, hS, Real.exp_add]
      exact mul_le_mul_of_nonneg_left hR1 (Real.exp_pos _).le
    have hE1 : 1 ≤ Real.exp (K.w * As + Λ) := Real.one_le_exp (by positivity)
    have hW0 : 0 ≤ W := by rw [hW]; positivity
    have h2W : 1 + (W + 1) ≤ 3 * Real.exp (K.w * As + Λ) := by linarith only [hWexp, hE1]
    have hpowA : (1 + (W + 1)) ^ A ≤ 3 ^ A * Real.exp (A * (K.w * As + Λ)) := by
      calc (1 + (W + 1)) ^ A ≤ (3 * Real.exp (K.w * As + Λ)) ^ A :=
            Real.rpow_le_rpow (by linarith only [hW0]) h2W hA
        _ = 3 ^ A * Real.exp (K.w * As + Λ) ^ A := Real.mul_rpow (by norm_num) (Real.exp_pos _).le
        _ = 3 ^ A * Real.exp (A * (K.w * As + Λ)) := by
            rw [← Real.exp_mul, mul_comm (K.w * As + Λ) A]
    have hHp : Hbar ^ p = Real.exp ((|Real.log (C₁ * 3 ^ A)| + A) * Λ + (A * K.w + p * K.h) * As) := by
      rw [hHbar, ← Real.exp_mul]
      congr 1
      rw [← K.hpκH, ← K.hph']; ring
    rw [hHp, div_eq_mul_inv, ← Real.exp_neg]
    have hK : 0 < C₁ * 3 ^ A := by positivity
    have hlog : Real.log (C₁ * 3 ^ A) ≤ |Real.log (C₁ * 3 ^ A)| * Λ := p7_le_abs_mul hΛ1
    have h1 : C₁ * (1 + (W + 1)) ^ A * Real.exp (-((|Real.log (C₁ * 3 ^ A)| + A) * Λ + (A * K.w + p * K.h) * As)) ≤
        C₁ * (3 ^ A * Real.exp (A * (K.w * As + Λ))) *
          Real.exp (-((|Real.log (C₁ * 3 ^ A)| + A) * Λ + (A * K.w + p * K.h) * As)) := by
      gcongr
    have h2 : C₁ * (3 ^ A * Real.exp (A * (K.w * As + Λ))) *
          Real.exp (-((|Real.log (C₁ * 3 ^ A)| + A) * Λ + (A * K.w + p * K.h) * As)) =
        Real.exp (Real.log (C₁ * 3 ^ A) - |Real.log (C₁ * 3 ^ A)| * Λ - p * K.h * As) := by
      have hX : A * (K.w * As + Λ) + -((|Real.log (C₁ * 3 ^ A)| + A) * Λ + (A * K.w + p * K.h) * As) =
          -(|Real.log (C₁ * 3 ^ A)| * Λ) - p * K.h * As := by ring
      calc C₁ * (3 ^ A * Real.exp (A * (K.w * As + Λ))) *
            Real.exp (-((|Real.log (C₁ * 3 ^ A)| + A) * Λ + (A * K.w + p * K.h) * As))
          = (C₁ * 3 ^ A) * Real.exp (A * (K.w * As + Λ) +
              -((|Real.log (C₁ * 3 ^ A)| + A) * Λ + (A * K.w + p * K.h) * As)) := by
            rw [Real.exp_add]; ring
        _ = Real.exp (Real.log (C₁ * 3 ^ A)) *
              Real.exp (-(|Real.log (C₁ * 3 ^ A)| * Λ) - p * K.h * As) := by
            rw [hX, Real.exp_log hK]
        _ = Real.exp (Real.log (C₁ * 3 ^ A) - |Real.log (C₁ * 3 ^ A)| * Λ - p * K.h * As) := by
            rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (Real.log (C₁ * 3 ^ A) - |Real.log (C₁ * 3 ^ A)| * Λ - p * K.h * As) ≤
        Real.exp (-(p * K.h * As)) := Real.exp_le_exp.mpr (by linarith only [hlog])
    linarith only [h1, h2, h3]
  -- covers
  have hcov : ∀ j < N, Cc * (1 + W) ^ d * Real.exp (-2 * (p7a K.L (j + 1) * n)) ≤
      Cc * 4 ^ d * R ^ d * Real.exp (-(1 * As)) := by
    intro j hj
    have hW1 : 1 + W ≤ 4 * R * S := by
      rw [hW]
      have h1 : 1 ≤ S * (R + 1) := by nlinarith
      nlinarith
    have hpow : (1 + W) ^ d ≤ 4 ^ d * R ^ d * Real.exp (K.w * As) ^ d := by
      calc (1 + W) ^ d ≤ (4 * R * S) ^ d := by
            apply pow_le_pow_left₀ _ hW1
            have : 0 ≤ W := by rw [hW]; positivity
            linarith only [this]
        _ = 4 ^ d * R ^ d * Real.exp (K.w * As) ^ d := by rw [mul_pow, mul_pow, hS]
    have hexpd : Real.exp (K.w * As) ^ d ≤ Real.exp As := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right K.hwd hAs0
      linarith only [this]
    have haj : As ≤ p7a K.L (j + 1) * n := by
      rw [hAs]; exact mul_le_mul_of_nonneg_right (hanti (by omega : j + 1 ≤ N)) hn0
    have hexp2 : Real.exp (-2 * (p7a K.L (j + 1) * n)) ≤ Real.exp (-2 * As) :=
      Real.exp_le_exp.mpr (by linarith only [haj])
    have h4R : (0 : ℝ) ≤ 4 ^ d * R ^ d := by positivity
    calc Cc * (1 + W) ^ d * Real.exp (-2 * (p7a K.L (j + 1) * n))
        ≤ Cc * (4 ^ d * R ^ d * Real.exp As) * Real.exp (-2 * As) := by
          apply mul_le_mul _ hexp2 (Real.exp_pos _).le (by positivity)
          apply mul_le_mul_of_nonneg_left _ hCc.le
          exact hpow.trans (mul_le_mul_of_nonneg_left hexpd h4R)
      _ = Cc * 4 ^ d * R ^ d * Real.exp (-(1 * As)) := by
          rw [show Cc * (4 ^ d * R ^ d * Real.exp As) * Real.exp (-2 * As) =
            Cc * 4 ^ d * R ^ d * (Real.exp As * Real.exp (-2 * As)) by ring, ← Real.exp_add]
          congr 2; ring
  -- cap
  have hcap : Ccp * Real.exp (-ccp * (⌈n⌉₊ : ℝ)) ≤ Ccp * Real.exp (-(ccp * n)) := by
    apply mul_le_mul_of_nonneg_left _ hCcp.le
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left (Nat.le_ceil n) hccp.le
    linarith only [this]
  -- the sum
  have hsum := p7_fail_sum d (N := N) (K1 := K.Cesc') (K2 := 1) (K3 := 1) (K4 := Cc * 4 ^ d) (K5 := Ccp)
    (r1 := pesc * K.w) (r2 := p * K.h) (r3 := K.c₀) (r4 := 1) (r5 := ccp) (C3 := K.C₃) (c3 := K.c₃)
    (M3 := K.M₃) (KN := K.KN) hR hδ hδ1 hAs hAsn hn0 haN K.hca0 K.hcp0 K.hcp1 K.hcp2 K.hcp3 K.hcp4 K.hcp5
    K.hCesc'0.le zero_le_one zero_le_one (by positivity) hCcp.le K.hKN0.le hNδ K.hM₃d K.hM₃0' K.hM₃1
    K.hKF K.hc₃1
  exact ⟨hesc, henv, hcov, hcap, hsum⟩

end HigherDimLQGContinuity
