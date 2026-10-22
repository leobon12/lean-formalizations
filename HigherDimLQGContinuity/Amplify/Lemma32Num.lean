import HigherDimLQGContinuity.Amplify.Analytic

/-!
# The numerical bookkeeping of Lemma 3.2 (packet P7)

Blueprint `a:lem32` (NA1 R8): with the bracket `Λ = 1 + log(1 + R) + log e⁻¹ + log q⁻¹` the confinement factor,
the confinement radius and the envelope threshold are chosen as
`S = e^{κ_S Λ}`, `W = S (R + 1)`, `H̄ = e^{κ_H Λ}` (`p7κS`, `p7κH`), and the band of Lemma 3.2 is `V = n/4`
(radii `[e^{-n/2}, e^{-n/4}]`). `p7_lemma32_numerics` proves, for `n ≥ C₃₂ Λ` (`p7C32`), all the numerical facts the
proof of Lemma 3.2 uses: each of the six failure probabilities is at most `q/8`, the band and cap conditions hold, and
the endpoint attachment costs at most `e`.

(This replaces the blueprint's `S = max(4, (8C_esc/q)^{1/p_esc})`, `H̄ = (8C₁(2+W)^A/q)^{1/p}` by exponentials of
`Λ`; the bounds are the same up to constants.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

/-- The exponent of the confinement factor `S = e^{κ_S Λ}`. -/
def p7κS (pesc Cesc : ℝ) : ℝ := (|Real.log (8 * Cesc)| + 2) / pesc + 3

/-- The exponent of the envelope threshold `H̄ = e^{κ_H Λ}`. -/
def p7κH (p C₁ A κS : ℝ) : ℝ := (|Real.log (8 * C₁ * 3 ^ A)| + A * (κS + 1) + 1) / p

/-- The depth constant `C₃₂` of Lemma 3.2. -/
def p7C32 (d : ℕ) (σ Cc Ccp ccp κS κH : ℝ) : ℝ :=
  8 + 2 * (|Real.log (8 * Cc * 2 ^ d)| + d * (κS + 1) + 1) + (|Real.log (8 * Ccp)| + 1) / ccp +
    (κS + 3) / 2 + 4 * (κH + 9) / σ

theorem p7κS_ge (pesc Cesc : ℝ) (hpesc : 0 < pesc) : 3 ≤ p7κS pesc Cesc := by
  unfold p7κS
  have : 0 ≤ (|Real.log (8 * Cesc)| + 2) / pesc := by positivity
  linarith

theorem p7κS_mul (pesc Cesc : ℝ) (hpesc : 0 < pesc) :
    pesc * p7κS pesc Cesc = |Real.log (8 * Cesc)| + 2 + 3 * pesc := by
  unfold p7κS
  field_simp

theorem p7κH_nonneg {p C₁ A κS : ℝ} (hp : 0 < p) (hA : 0 ≤ A) (hκS : 0 ≤ κS) :
    0 ≤ p7κH p C₁ A κS := by
  unfold p7κH
  positivity

theorem p7κH_mul (p C₁ A κS : ℝ) (hp : 0 < p) :
    p * p7κH p C₁ A κS = |Real.log (8 * C₁ * 3 ^ A)| + A * (κS + 1) + 1 := by
  unfold p7κH
  field_simp

theorem p7C32_pos (d : ℕ) {σ Cc Ccp ccp κS κH : ℝ} (hσ : 0 < σ) (hccp : 0 < ccp) (hκS : 0 ≤ κS)
    (hκH : 0 ≤ κH) : 0 < p7C32 d σ Cc Ccp ccp κS κH := by
  unfold p7C32
  have h1 : 0 ≤ 2 * (|Real.log (8 * Cc * 2 ^ d)| + d * (κS + 1) + 1) := by positivity
  have h2 : 0 ≤ (|Real.log (8 * Ccp)| + 1) / ccp := by positivity
  have h3 : 0 ≤ (κS + 3) / 2 := by positivity
  have h4 : 0 ≤ 4 * (κH + 9) / σ := by positivity
  linarith

/-- `log 3 ≤ 2`, `log 4 ≤ 2` and `log 8 ≤ 7` (from `log x ≤ x - 1`). -/
theorem p7_log_three_le : Real.log 3 ≤ 2 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  linarith

theorem p7_log_eight_le : Real.log 8 ≤ 7 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
  linarith

theorem p7_log_four_le : Real.log 4 ≤ 2 := by
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith

/-- A summand of a nonnegative sum times `Λ ≥ 0`. -/
theorem p7_summand_mul_le {a s Λ n : ℝ} (has : a ≤ s) (hΛ : 0 ≤ Λ) (h : s * Λ ≤ n) : a * Λ ≤ n :=
  (mul_le_mul_of_nonneg_right has hΛ).trans h

/-- **Numerics of Lemma 3.2** (abstract form: `κ_S`, `κ_H` are given with their defining identities). -/
theorem p7_lemma32_numerics_abs (d : ℕ) {pesc Cesc p C₁ A σ Cc Ccp ccp κS κH : ℝ}
    (hpesc : 0 < pesc) (hCesc : 0 < Cesc) (hC₁ : 0 < C₁) (hA : 0 ≤ A) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hCc : 0 < Cc) (hCcp : 0 < Ccp) (hccp : 0 < ccp)
    (hκS3 : 3 ≤ κS) (hpκS : pesc * κS = |Real.log (8 * Cesc)| + 2 + 3 * pesc)
    (hκH0 : 0 ≤ κH) (hpκH : p * κH = |Real.log (8 * C₁ * 3 ^ A)| + A * (κS + 1) + 1)
    {R e q n Λ S W Hbar : ℝ} (hR : 0 ≤ R) (he : 0 < e) (he1 : e ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1)
    (hΛ : Λ = p7Lam R e q) (hSdef : S = Real.exp (κS * Λ)) (hWdef : W = S * (R + 1))
    (hHdef : Hbar = Real.exp (κH * Λ))
    (hn : (8 + 2 * (|Real.log (8 * Cc * 2 ^ d)| + d * (κS + 1) + 1) + (|Real.log (8 * Ccp)| + 1) / ccp +
      (κS + 3) / 2 + 4 * (κH + 9) / σ) * Λ ≤ n) :
    4 ≤ S ∧ Cesc * S ^ (-pesc) ≤ q / 8 ∧ C₁ * (1 + (W + 1)) ^ A / Hbar ^ p ≤ q / 8 ∧
      Cc * (1 + W) ^ d * Real.exp (-2 * (n / 4)) ≤ q / 8 ∧
      Ccp * Real.exp (-ccp * (⌈n⌉₊ : ℝ)) ≤ q / 8 ∧
      Real.log 4 ≤ n / 4 ∧ 1 ≤ n / 4 ∧ 1 ≤ ⌈n⌉₊ ∧ Real.log (1 + (W + 1)) ≤ 2 * (⌈n⌉₊ : ℝ) ∧
      2 * (n / 4) ≤ (⌈n⌉₊ : ℝ) ∧ 2 * (Hbar * (4 * Real.exp (-(n / 4))) ^ σ) ≤ e ∧ 1 ≤ Hbar ∧
      1 ≤ n := by
  obtain ⟨hΛ1, hΛR, hΛe, hΛq⟩ := p7Lam_spec hR he he1 hq hq1
  rw [← hΛ] at hΛ1 hΛR hΛe hΛq
  have hΛ0 : 0 ≤ Λ := by linarith
  -- the summands of the depth constant
  set T1 := 2 * (|Real.log (8 * Cc * 2 ^ d)| + d * (κS + 1) + 1) with hT1def
  set T2 := (|Real.log (8 * Ccp)| + 1) / ccp with hT2def
  set T3 := (κS + 3) / 2 with hT3def
  set T4 := 4 * (κH + 9) / σ with hT4def
  have hT1 : 0 ≤ T1 := by rw [hT1def]; positivity
  have hT2 : 0 ≤ T2 := by rw [hT2def]; positivity
  have hT3 : 0 ≤ T3 := by rw [hT3def]; positivity
  have hT4 : 0 ≤ T4 := by rw [hT4def]; positivity
  have hn8 : 8 * Λ ≤ n :=
    p7_summand_mul_le (by linarith only [hT1, hT2, hT3, hT4]) hΛ0 hn
  have hn1 : T1 * Λ ≤ n := p7_summand_mul_le (by linarith only [hT1, hT2, hT3, hT4]) hΛ0 hn
  have hn2 : T2 * Λ ≤ n := p7_summand_mul_le (by linarith only [hT1, hT2, hT3, hT4]) hΛ0 hn
  have hn3 : T3 * Λ ≤ n := p7_summand_mul_le (by linarith only [hT1, hT2, hT3, hT4]) hΛ0 hn
  have hn4 : T4 * Λ ≤ n := p7_summand_mul_le (by linarith only [hT1, hT2, hT3, hT4]) hΛ0 hn
  have hn0 : 8 ≤ n := by linarith only [hn8, hΛ1]
  -- basic bounds on `S`, `W`
  have hκSΛ : 3 ≤ κS * Λ := by
    have := mul_le_mul hκS3 hΛ1 zero_le_one (by linarith)
    linarith only [this]
  have hS4 : 4 ≤ S := by
    rw [hSdef]
    have h := Real.add_one_le_exp (κS * Λ)
    linarith only [h, hκSΛ]
  have hR1 : 1 + R ≤ Real.exp Λ := p7_le_exp_of_log_le (by linarith) hΛR
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hWexp : W ≤ Real.exp ((κS + 1) * Λ) := by
    rw [hWdef, hSdef, add_mul, one_mul, Real.exp_add]
    have : R + 1 ≤ Real.exp Λ := by linarith only [hR1]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  have hE1 : 1 ≤ Real.exp ((κS + 1) * Λ) := Real.one_le_exp (by positivity)
  have hHbar1 : 1 ≤ Hbar := by rw [hHdef]; exact Real.one_le_exp (by positivity)
  have hq' := p7_exp_neg_le_of_log_inv_le hq hΛq
  -- (n2) escape failure
  have hesc : Cesc * S ^ (-pesc) ≤ q / 8 := by
    have hpow : S ^ (-pesc) = Real.exp (-(pesc * (κS * Λ))) := by
      rw [hSdef, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      ring_nf
    rw [hpow]
    have hK : 0 < 8 * Cesc := by positivity
    have hlog : Real.log (8 * Cesc) + Λ ≤ pesc * (κS * Λ) := by
      have h1 : Real.log (8 * Cesc) ≤ |Real.log (8 * Cesc)| * Λ := p7_le_abs_mul hΛ1
      have h3 : pesc * (κS * Λ) = (|Real.log (8 * Cesc)| + 2 + 3 * pesc) * Λ := by
        rw [← mul_assoc, hpκS]
      rw [h3]
      have h4 : 0 ≤ 3 * pesc * Λ := by positivity
      linarith only [h1, hΛ1, h4]
    have h := p7_mul_exp_le_exp hK hlog
    linarith only [h, hq']
  -- (n3) envelope failure
  have henv : C₁ * (1 + (W + 1)) ^ A / Hbar ^ p ≤ q / 8 := by
    have h2W : 1 + (W + 1) ≤ 3 * Real.exp ((κS + 1) * Λ) := by linarith only [hWexp, hE1]
    have hpowA : (1 + (W + 1)) ^ A ≤ 3 ^ A * Real.exp (A * ((κS + 1) * Λ)) := by
      calc (1 + (W + 1)) ^ A ≤ (3 * Real.exp ((κS + 1) * Λ)) ^ A :=
            Real.rpow_le_rpow (by positivity) h2W hA
        _ = 3 ^ A * Real.exp ((κS + 1) * Λ) ^ A := Real.mul_rpow (by norm_num) (Real.exp_pos _).le
        _ = 3 ^ A * Real.exp (A * ((κS + 1) * Λ)) := by
            rw [← Real.exp_mul, mul_comm ((κS + 1) * Λ) A]
    have hHp : Hbar ^ p = Real.exp (p * (κH * Λ)) := by
      rw [hHdef, ← Real.exp_mul, mul_comm (κH * Λ) p]
    rw [hHp, div_eq_mul_inv, ← Real.exp_neg]
    have hK : 0 < 8 * C₁ * 3 ^ A := by positivity
    have hlog : Real.log (8 * C₁ * 3 ^ A) + Λ ≤ p * (κH * Λ) - A * ((κS + 1) * Λ) := by
      have h1 : Real.log (8 * C₁ * 3 ^ A) ≤ |Real.log (8 * C₁ * 3 ^ A)| * Λ := p7_le_abs_mul hΛ1
      have h3 : p * (κH * Λ) = (|Real.log (8 * C₁ * 3 ^ A)| + A * (κS + 1) + 1) * Λ := by
        rw [← mul_assoc, hpκH]
      rw [h3]
      have h5 : (|Real.log (8 * C₁ * 3 ^ A)| + A * (κS + 1) + 1) * Λ =
          |Real.log (8 * C₁ * 3 ^ A)| * Λ + A * ((κS + 1) * Λ) + Λ := by ring
      rw [h5]
      linarith only [h1]
    have h := p7_mul_exp_le_exp hK hlog
    have hexp : Real.exp (-(p * (κH * Λ) - A * ((κS + 1) * Λ))) =
        Real.exp (A * ((κS + 1) * Λ)) * Real.exp (-(p * (κH * Λ))) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmain : C₁ * (1 + (W + 1)) ^ A * Real.exp (-(p * (κH * Λ))) ≤
        C₁ * (3 ^ A * Real.exp (A * ((κS + 1) * Λ))) * Real.exp (-(p * (κH * Λ))) := by
      gcongr
    have hfin : 8 * (C₁ * (3 ^ A * Real.exp (A * ((κS + 1) * Λ))) * Real.exp (-(p * (κH * Λ)))) ≤ q := by
      calc 8 * (C₁ * (3 ^ A * Real.exp (A * ((κS + 1) * Λ))) * Real.exp (-(p * (κH * Λ))))
          = 8 * C₁ * 3 ^ A * Real.exp (-(p * (κH * Λ) - A * ((κS + 1) * Λ))) := by
            rw [hexp]; ring
        _ ≤ Real.exp (-Λ) := h
        _ ≤ q := hq'
    linarith only [hmain, hfin]
  -- (n4) cover failure
  have hcov : Cc * (1 + W) ^ d * Real.exp (-2 * (n / 4)) ≤ q / 8 := by
    have h1W : 1 + W ≤ 2 * Real.exp ((κS + 1) * Λ) := by linarith only [hWexp, hE1]
    have hpowd : (1 + W) ^ d ≤ 2 ^ d * Real.exp (d * ((κS + 1) * Λ)) := by
      calc (1 + W) ^ d ≤ (2 * Real.exp ((κS + 1) * Λ)) ^ d :=
            pow_le_pow_left₀ (by linarith only [hW0]) h1W d
        _ = 2 ^ d * Real.exp (d * ((κS + 1) * Λ)) := by rw [mul_pow, ← Real.exp_nat_mul]
    have hK : 0 < 8 * Cc * 2 ^ d := by positivity
    have hlog : Real.log (8 * Cc * 2 ^ d) + Λ ≤ n / 2 - d * ((κS + 1) * Λ) := by
      have h1 : Real.log (8 * Cc * 2 ^ d) ≤ |Real.log (8 * Cc * 2 ^ d)| * Λ := p7_le_abs_mul hΛ1
      have h2 : T1 * Λ = 2 * (|Real.log (8 * Cc * 2 ^ d)| * Λ + d * ((κS + 1) * Λ) + Λ) := by
        rw [hT1def]; ring
      linarith only [h1, h2, hn1]
    have h := p7_mul_exp_le_exp hK hlog
    have hexp : Real.exp (-(n / 2 - d * ((κS + 1) * Λ))) =
        Real.exp (d * ((κS + 1) * Λ)) * Real.exp (-2 * (n / 4)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmain : Cc * (1 + W) ^ d * Real.exp (-2 * (n / 4)) ≤
        Cc * (2 ^ d * Real.exp (d * ((κS + 1) * Λ))) * Real.exp (-2 * (n / 4)) := by
      gcongr
    have hfin : 8 * (Cc * (2 ^ d * Real.exp (d * ((κS + 1) * Λ))) * Real.exp (-2 * (n / 4))) ≤ q := by
      calc 8 * (Cc * (2 ^ d * Real.exp (d * ((κS + 1) * Λ))) * Real.exp (-2 * (n / 4)))
          = 8 * Cc * 2 ^ d * Real.exp (-(n / 2 - d * ((κS + 1) * Λ))) := by rw [hexp]; ring
        _ ≤ Real.exp (-Λ) := h
        _ ≤ q := hq'
    linarith only [hmain, hfin]
  -- ceilings
  have hN : n ≤ (⌈n⌉₊ : ℝ) := Nat.le_ceil n
  have hN1 : 1 ≤ ⌈n⌉₊ := by
    have h1 : (1 : ℝ) ≤ (⌈n⌉₊ : ℝ) := by linarith only [hN, hn0]
    exact_mod_cast h1
  -- (n5) cap failure
  have hcap : Ccp * Real.exp (-ccp * (⌈n⌉₊ : ℝ)) ≤ q / 8 := by
    have hK : 0 < 8 * Ccp := by positivity
    have hlog : Real.log (8 * Ccp) + Λ ≤ ccp * n := by
      have h1 : Real.log (8 * Ccp) ≤ |Real.log (8 * Ccp)| * Λ := p7_le_abs_mul hΛ1
      have h2 : (|Real.log (8 * Ccp)| + 1) * Λ ≤ ccp * n := by
        have h3 : T2 * Λ * ccp = (|Real.log (8 * Ccp)| + 1) * Λ := by
          rw [hT2def]; field_simp
        have h4 : T2 * Λ * ccp ≤ n * ccp := mul_le_mul_of_nonneg_right hn2 hccp.le
        linarith only [h3, h4]
      linarith only [h1, h2]
    have h := p7_mul_exp_le_exp hK hlog
    have hmono : Real.exp (-ccp * (⌈n⌉₊ : ℝ)) ≤ Real.exp (-(ccp * n)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hN hccp.le
      linarith only [this]
    have hfin : 8 * (Ccp * Real.exp (-(ccp * n))) ≤ q := by linarith only [h, hq']
    have : Ccp * Real.exp (-ccp * (⌈n⌉₊ : ℝ)) ≤ Ccp * Real.exp (-(ccp * n)) :=
      mul_le_mul_of_nonneg_left hmono hCcp.le
    linarith only [this, hfin]
  -- (n6), (n7)
  have hl4 := p7_log_four_le
  have hV4 : Real.log 4 ≤ n / 4 := by linarith only [hl4, hn0]
  have hV1 : 1 ≤ n / 4 := by linarith only [hn0]
  have hlogW : Real.log (1 + (W + 1)) ≤ 2 * (⌈n⌉₊ : ℝ) := by
    have h2W : 1 + (W + 1) ≤ 3 * Real.exp ((κS + 1) * Λ) := by linarith only [hWexp, hE1]
    have hl : Real.log (1 + (W + 1)) ≤ Real.log 3 + (κS + 1) * Λ := by
      calc Real.log (1 + (W + 1)) ≤ Real.log (3 * Real.exp ((κS + 1) * Λ)) :=
            Real.log_le_log (by linarith only [hW0]) h2W
        _ = Real.log 3 + (κS + 1) * Λ := by
            rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    have h3 := p7_log_three_le
    have h5 : T3 * Λ = ((κS + 1) * Λ + 2 * Λ) / 2 := by rw [hT3def]; ring
    linarith only [hl, h3, h5, hn3, hΛ1, hN]
  have hNV : 2 * (n / 4) ≤ (⌈n⌉₊ : ℝ) := by linarith only [hN, hn0]
  -- (n8) endpoint attachment
  have hatt : 2 * (Hbar * (4 * Real.exp (-(n / 4))) ^ σ) ≤ e := by
    have hpow : (4 * Real.exp (-(n / 4))) ^ σ ≤ 4 * Real.exp (-(σ * (n / 4))) := by
      rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
      have h4 : (4 : ℝ) ^ σ ≤ 4 := by
        calc (4 : ℝ) ^ σ ≤ (4 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
          _ = 4 := Real.rpow_one 4
      have : Real.exp (-(n / 4) * σ) = Real.exp (-(σ * (n / 4))) := by
        congr 1; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    have hK : (0 : ℝ) < 8 := by norm_num
    have hlog : Real.log 8 + Λ ≤ σ * (n / 4) - κH * Λ := by
      have h1 := p7_log_eight_le
      have h2 : (κH + 9) * Λ ≤ σ * (n / 4) := by
        have h3 : T4 * Λ * σ = 4 * ((κH + 9) * Λ) := by rw [hT4def]; field_simp
        have h4 : T4 * Λ * σ ≤ n * σ := mul_le_mul_of_nonneg_right hn4 hσ.le
        linarith only [h3, h4]
      have h6 : (κH + 9) * Λ = κH * Λ + 9 * Λ := by ring
      linarith only [h1, h2, h6, hΛ1]
    have h := p7_mul_exp_le_exp hK hlog
    have he' := p7_exp_neg_le_of_log_inv_le he hΛe
    have hexp : Real.exp (-(σ * (n / 4) - κH * Λ)) = Hbar * Real.exp (-(σ * (n / 4))) := by
      rw [hHdef, ← Real.exp_add]; congr 1; ring
    have hHb0 : 0 ≤ Hbar := by linarith only [hHbar1]
    calc 2 * (Hbar * (4 * Real.exp (-(n / 4))) ^ σ) ≤
          2 * (Hbar * (4 * Real.exp (-(σ * (n / 4))))) := by
          gcongr
      _ = 8 * Real.exp (-(σ * (n / 4) - κH * Λ)) := by rw [hexp]; ring
      _ ≤ Real.exp (-Λ) := h
      _ ≤ e := he'
  exact ⟨hS4, hesc, henv, hcov, hcap, hV4, hV1, hN1, hlogW, hNV, hatt, hHbar1, by linarith only [hn0]⟩

end HigherDimLQGContinuity
