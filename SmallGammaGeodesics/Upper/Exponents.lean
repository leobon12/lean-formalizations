import SmallGammaGeodesics.Upper.Basic

/-!
# The exponents under Route F (blueprint `lem:exponents`, Table `tab:exponents`; BP2 detail D10;
packet P-U2)

`probe_exponents`: for all small `ξ > 0`, every level `j ≤ J(ξ)` and every `R ∈ [ξ^{2/3}, 2ξ^{a/2}]`
(`a = 99/100`), with `r = c_β R ℓ_j^{1/8}`, `Δ = 3ξ^a`, `M = √3 ξ^{a/2}`:
(X1) `ξ ≤ 1/64`, `ξ^a ≤ 1/100`; (X2) `Δ ≤ ℓ_j`, `M ≤ ℓ_j/16`; (X3) `|c| r ≤ ε ℓ_j`;
(X4) the error of Lemma T is at most `(|c|/8) r²/ℓ_j`; (X5) `C_R(√(ℓ_J ξ^a) + ξ^a) ≤ (3/4) ξ^{2/3}`;
(X6) `1 + log(1/ℓ_j) ≤ 2 log(1/ξ)`.

Proof: with `X = ξ^{1/4800}` every exponent of Table `tab:exponents` becomes a natural power
(`ξ^a = X^{4752}`, `ξ^{a/2} = X^{2376}`, `ξ^{2/3} = X^{3200}`, `ξ^{3/8} = X^{1800}`,
`ξ^{19/1200} = X^{76}`), and with `L = ℓ_j^{1/8}` one has `ℓ_j = L⁸` and `X^{225}/2 ≤ L ≤ 1`
(from P-U0's `ell_Jxi_bounds`). Each requirement then reduces to a bound `K X ≤ 1` (or `≤ c_β`,
`≤ ε`) with `K` independent of `j` and `R`, which holds for `X ≤ X₀`; the margins used are
`X^{1903}`, `X^{103}` (the binding one, `103/4800 = 2/3·…` of Table `tab:exponents`), and `X^{1152}`
for the three remaining error terms (cruder than the table, using `L ≤ 1`). (X5) is P-U0's
`sqrt_ell_Jxi_mul_add_le` and (X6) P-U0's `log_inv_ell_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace SmallGammaGeodesics

/-- `√3 ≤ 2`. -/
theorem sqrt_three_le_two : Real.sqrt 3 ≤ 2 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- Error terms (t1), (t2) of Lemma `lem:exponents`. -/
theorem exponents_t12 {X L R cβ C : ℝ} (hX0 : 0 < X) (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hLX : X ^ 225 / 2 ≤ L) (hR1 : X ^ 3200 ≤ R) (hR2 : R ≤ 2 * X ^ 2376)
    (hcβ : 0 < cβ) (hC : 0 ≤ C) (hs0 : 10000 * X ≤ 1)
    (hs1 : 240 * 2 ^ 17 * (C + 1) * X ≤ cβ) :
    40 * (C + 1) * (Real.sqrt 3 * X ^ 2376 * (3 * X ^ 4752) * L ^ 8) ≤
        cβ * R * L * (L ^ 8) ^ 2 ∧
      40 * (C + 1) * (Real.sqrt 3 * X ^ 2376) ^ 3 ≤ cβ * R * L * (L ^ 8) ^ 2 := by
  have hX1 : X ≤ 1 := by linarith
  have hpow : ∀ k : ℕ, k ≠ 0 → X ^ k ≤ X := fun k hk => pow_le_of_le_one hX0.le hX1 hk
  have hLn : ∀ n : ℕ, (X ^ 225 / 2) ^ n ≤ L ^ n := fun n =>
    pow_le_pow_left₀ (by positivity) hLX n
  have hs3' : Real.sqrt 3 ≤ 2 := sqrt_three_le_two
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR1
  have hC1 : 0 < C + 1 := by linarith
  have hr0 : 0 < cβ * R * L := by positivity
  have hM2 : (Real.sqrt 3 * X ^ 2376) ^ 2 = 3 * X ^ 4752 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring
  have hM3 : (Real.sqrt 3 * X ^ 2376) ^ 3 = 3 * Real.sqrt 3 * X ^ 7128 := by
    have e : (Real.sqrt 3 * X ^ 2376) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 * X ^ 7128 := by ring
    rw [e, Real.sq_sqrt (by norm_num)]
  have hMle : Real.sqrt 3 * X ^ 2376 ≤ 2 * X ^ 2376 :=
    mul_le_mul_of_nonneg_right hs3' (by positivity)
  have hrle : cβ * R * L ≤ 2 * cβ * X ^ 2376 := by
    calc cβ * R * L ≤ cβ * (2 * X ^ 2376) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hR2 hcβ.le) hL1 hL0.le (by positivity)
      _ = 2 * cβ * X ^ 2376 := by ring
  have hL16 : X ^ 3600 / 2 ^ 16 ≤ L ^ 16 := by
    have := hLn 16
    have e : (X ^ 225 / 2) ^ 16 = X ^ 3600 / 2 ^ 16 := by ring
    rwa [e] at this
  have hsmall : ∀ K : ℝ, 0 ≤ K → 2 ^ 16 * K * X ≤ 1 → K * X ^ 4752 ≤ L ^ 16 := by
    intro K hK hKX
    have h1 : X ^ 1152 ≤ X := hpow 1152 (by norm_num)
    calc K * X ^ 4752 = (K * X ^ 1152) * X ^ 3600 := by ring
      _ ≤ (K * X) * X ^ 3600 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK) (by positivity)
      _ ≤ (1 / 2 ^ 16) * X ^ 3600 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [le_div_iff₀ (by norm_num)]
          linarith
      _ = X ^ 3600 / 2 ^ 16 := by ring
      _ ≤ L ^ 16 := hL16
  have hrl : cβ * R * L * (L ^ 8) ^ 2 = cβ * R * L ^ 17 := by ring
  have hRL17 : cβ * X ^ 3200 * L ^ 17 ≤ cβ * R * L ^ 17 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR1 hcβ.le) (by positivity)
  -- (t1)
  have t1 : 40 * (C + 1) * (Real.sqrt 3 * X ^ 2376 * (3 * X ^ 4752) * L ^ 8) ≤
      cβ * R * L * (L ^ 8) ^ 2 := by
    have hL9 : X ^ 2025 / 512 ≤ L ^ 9 := by
      have := hLn 9
      have e : (X ^ 225 / 2) ^ 9 = X ^ 2025 / 512 := by ring
      rwa [e] at this
    have h1 : X ^ 1903 ≤ X := hpow 1903 (by norm_num)
    have hCX : 0 ≤ (C + 1) * X := by positivity
    have h2 : 240 * (C + 1) * X ^ 1903 ≤ cβ / 512 := by
      have h3 : 240 * (C + 1) * X ^ 1903 ≤ 240 * (C + 1) * X :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    calc 40 * (C + 1) * (Real.sqrt 3 * X ^ 2376 * (3 * X ^ 4752) * L ^ 8)
        = (120 * (C + 1) * X ^ 1903) * Real.sqrt 3 * (X ^ 5225 * L ^ 8) := by ring
      _ ≤ (120 * (C + 1) * X ^ 1903) * 2 * (X ^ 5225 * L ^ 8) := by
          gcongr
      _ = (240 * (C + 1) * X ^ 1903) * (X ^ 5225 * L ^ 8) := by ring
      _ ≤ (cβ / 512) * (X ^ 5225 * L ^ 8) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = cβ * X ^ 3200 * (X ^ 2025 / 512) * L ^ 8 := by ring
      _ ≤ cβ * X ^ 3200 * L ^ 9 * L ^ 8 := by gcongr
      _ = cβ * X ^ 3200 * L ^ 17 := by ring
      _ ≤ cβ * R * L ^ 17 := hRL17
      _ = cβ * R * L * (L ^ 8) ^ 2 := hrl.symm
  -- (t2)
  have t2 : 40 * (C + 1) * (Real.sqrt 3 * X ^ 2376) ^ 3 ≤ cβ * R * L * (L ^ 8) ^ 2 := by
    have hL17 : X ^ 3825 / 2 ^ 17 ≤ L ^ 17 := by
      have := hLn 17
      have e : (X ^ 225 / 2) ^ 17 = X ^ 3825 / 2 ^ 17 := by ring
      rwa [e] at this
    have h1 : X ^ 103 ≤ X := hpow 103 (by norm_num)
    have h2 : 240 * (C + 1) * X ^ 103 ≤ cβ / 2 ^ 17 := by
      have h3 : 240 * (C + 1) * X ^ 103 ≤ 240 * (C + 1) * X :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    rw [hM3]
    calc 40 * (C + 1) * (3 * Real.sqrt 3 * X ^ 7128)
        = (120 * (C + 1) * X ^ 103) * Real.sqrt 3 * X ^ 7025 := by ring
      _ ≤ (120 * (C + 1) * X ^ 103) * 2 * X ^ 7025 := by gcongr
      _ = (240 * (C + 1) * X ^ 103) * X ^ 7025 := by ring
      _ ≤ (cβ / 2 ^ 17) * X ^ 7025 := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = cβ * X ^ 3200 * (X ^ 3825 / 2 ^ 17) := by ring
      _ ≤ cβ * X ^ 3200 * L ^ 17 := by gcongr
      _ ≤ cβ * R * L ^ 17 := hRL17
      _ = cβ * R * L * (L ^ 8) ^ 2 := hrl.symm
  exact ⟨t1, t2⟩

/-- Error terms (t3)–(t5) of Lemma `lem:exponents`. -/
theorem exponents_t345 {X L R κ cβ C : ℝ} (hX0 : 0 < X) (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hLX : X ^ 225 / 2 ≤ L) (hR1 : X ^ 3200 ≤ R) (hR2 : R ≤ 2 * X ^ 2376) (hκ : 0 ≤ κ)
    (hcβ : 0 < cβ) (hC : 0 ≤ C) (hs0 : 10000 * X ≤ 1)
    (hs2 : 120 * 2 ^ 16 * κ * (C + 1) * X ≤ 1) (hs3 : 160 * 2 ^ 16 * (C + 1) * κ ^ 2 * cβ * X ≤ 1)
    (hs4 : 160 * 2 ^ 16 * (C + 1) * κ ^ 3 * cβ ^ 2 * X ≤ 1) :
    40 * (C + 1) * (κ * (cβ * R * L) * (Real.sqrt 3 * X ^ 2376) ^ 2) ≤
        cβ * R * L * (L ^ 8) ^ 2 ∧
      40 * (C + 1) * ((κ * (cβ * R * L)) ^ 2 * (Real.sqrt 3 * X ^ 2376)) ≤
        cβ * R * L * (L ^ 8) ^ 2 ∧
      40 * (C + 1) * (κ * (cβ * R * L)) ^ 3 ≤ cβ * R * L * (L ^ 8) ^ 2 := by
  have hX1 : X ≤ 1 := by linarith
  have hpow : ∀ k : ℕ, k ≠ 0 → X ^ k ≤ X := fun k hk => pow_le_of_le_one hX0.le hX1 hk
  have hLn : ∀ n : ℕ, (X ^ 225 / 2) ^ n ≤ L ^ n := fun n =>
    pow_le_pow_left₀ (by positivity) hLX n
  have hs3' : Real.sqrt 3 ≤ 2 := sqrt_three_le_two
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR1
  have hC1 : 0 < C + 1 := by linarith
  have hr0 : 0 < cβ * R * L := by positivity
  have hM2 : (Real.sqrt 3 * X ^ 2376) ^ 2 = 3 * X ^ 4752 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring
  have hM3 : (Real.sqrt 3 * X ^ 2376) ^ 3 = 3 * Real.sqrt 3 * X ^ 7128 := by
    have e : (Real.sqrt 3 * X ^ 2376) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 * X ^ 7128 := by ring
    rw [e, Real.sq_sqrt (by norm_num)]
  have hMle : Real.sqrt 3 * X ^ 2376 ≤ 2 * X ^ 2376 :=
    mul_le_mul_of_nonneg_right hs3' (by positivity)
  have hrle : cβ * R * L ≤ 2 * cβ * X ^ 2376 := by
    calc cβ * R * L ≤ cβ * (2 * X ^ 2376) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hR2 hcβ.le) hL1 hL0.le (by positivity)
      _ = 2 * cβ * X ^ 2376 := by ring
  have hL16 : X ^ 3600 / 2 ^ 16 ≤ L ^ 16 := by
    have := hLn 16
    have e : (X ^ 225 / 2) ^ 16 = X ^ 3600 / 2 ^ 16 := by ring
    rwa [e] at this
  have hsmall : ∀ K : ℝ, 0 ≤ K → 2 ^ 16 * K * X ≤ 1 → K * X ^ 4752 ≤ L ^ 16 := by
    intro K hK hKX
    have h1 : X ^ 1152 ≤ X := hpow 1152 (by norm_num)
    calc K * X ^ 4752 = (K * X ^ 1152) * X ^ 3600 := by ring
      _ ≤ (K * X) * X ^ 3600 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK) (by positivity)
      _ ≤ (1 / 2 ^ 16) * X ^ 3600 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [le_div_iff₀ (by norm_num)]
          linarith
      _ = X ^ 3600 / 2 ^ 16 := by ring
      _ ≤ L ^ 16 := hL16
  have hrl : cβ * R * L * (L ^ 8) ^ 2 = cβ * R * L ^ 17 := by ring
  have hRL17 : cβ * X ^ 3200 * L ^ 17 ≤ cβ * R * L ^ 17 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR1 hcβ.le) (by positivity)
  -- (t3)
  have t3 : 40 * (C + 1) * (κ * (cβ * R * L) * (Real.sqrt 3 * X ^ 2376) ^ 2) ≤
      cβ * R * L * (L ^ 8) ^ 2 := by
    have h1 : (120 * κ * (C + 1)) * X ^ 4752 ≤ L ^ 16 :=
      hsmall _ (by positivity) (by linarith)
    rw [hM2]
    calc 40 * (C + 1) * (κ * (cβ * R * L) * (3 * X ^ 4752))
        = cβ * R * L * ((120 * κ * (C + 1)) * X ^ 4752) := by ring
      _ ≤ cβ * R * L * L ^ 16 := mul_le_mul_of_nonneg_left h1 hr0.le
      _ = cβ * R * L * (L ^ 8) ^ 2 := by ring
  -- (t4)
  have t4 : 40 * (C + 1) * ((κ * (cβ * R * L)) ^ 2 * (Real.sqrt 3 * X ^ 2376)) ≤
      cβ * R * L * (L ^ 8) ^ 2 := by
    have h1 : (160 * (C + 1) * κ ^ 2 * cβ) * X ^ 4752 ≤ L ^ 16 :=
      hsmall _ (by positivity) (by linarith)
    have h2 : 40 * (C + 1) * κ ^ 2 * (cβ * R * L) * (Real.sqrt 3 * X ^ 2376) ≤
        (160 * (C + 1) * κ ^ 2 * cβ) * X ^ 4752 := by
      calc 40 * (C + 1) * κ ^ 2 * (cβ * R * L) * (Real.sqrt 3 * X ^ 2376)
          ≤ 40 * (C + 1) * κ ^ 2 * (2 * cβ * X ^ 2376) * (2 * X ^ 2376) := by
            gcongr
        _ = (160 * (C + 1) * κ ^ 2 * cβ) * X ^ 4752 := by ring
    calc 40 * (C + 1) * ((κ * (cβ * R * L)) ^ 2 * (Real.sqrt 3 * X ^ 2376))
        = cβ * R * L * (40 * (C + 1) * κ ^ 2 * (cβ * R * L) * (Real.sqrt 3 * X ^ 2376)) := by
          ring
      _ ≤ cβ * R * L * L ^ 16 := mul_le_mul_of_nonneg_left (h2.trans h1) hr0.le
      _ = cβ * R * L * (L ^ 8) ^ 2 := by ring
  -- (t5)
  have t5 : 40 * (C + 1) * (κ * (cβ * R * L)) ^ 3 ≤ cβ * R * L * (L ^ 8) ^ 2 := by
    have h1 : (160 * (C + 1) * κ ^ 3 * cβ ^ 2) * X ^ 4752 ≤ L ^ 16 :=
      hsmall _ (by positivity) (by linarith)
    have h2 : 40 * (C + 1) * κ ^ 3 * (cβ * R * L) ^ 2 ≤
        (160 * (C + 1) * κ ^ 3 * cβ ^ 2) * X ^ 4752 := by
      calc 40 * (C + 1) * κ ^ 3 * (cβ * R * L) ^ 2
          ≤ 40 * (C + 1) * κ ^ 3 * (2 * cβ * X ^ 2376) ^ 2 := by
            gcongr
        _ = (160 * (C + 1) * κ ^ 3 * cβ ^ 2) * X ^ 4752 := by ring
    calc 40 * (C + 1) * (κ * (cβ * R * L)) ^ 3
        = cβ * R * L * (40 * (C + 1) * κ ^ 3 * (cβ * R * L) ^ 2) := by ring
      _ ≤ cβ * R * L * L ^ 16 := mul_le_mul_of_nonneg_left (h2.trans h1) hr0.le
      _ = cβ * R * L * (L ^ 8) ^ 2 := by ring
  exact ⟨t3, t4, t5⟩

/-- Combination of the error terms of Lemma `lem:exponents` ((X4)). -/
theorem exponents_err {r M Δ ℓ κ C : ℝ} (hr0 : 0 < r) (hM0 : 0 ≤ M) (hΔ0 : 0 ≤ Δ) (hℓ0 : 0 < ℓ)
    (hκ : 0 ≤ κ)
    (t1 : 40 * (C + 1) * (M * Δ * ℓ) ≤ r * ℓ ^ 2) (t2 : 40 * (C + 1) * M ^ 3 ≤ r * ℓ ^ 2)
    (t3 : 40 * (C + 1) * (κ * r * M ^ 2) ≤ r * ℓ ^ 2)
    (t4 : 40 * (C + 1) * ((κ * r) ^ 2 * M) ≤ r * ℓ ^ 2)
    (t5 : 40 * (C + 1) * (κ * r) ^ 3 ≤ r * ℓ ^ 2) :
    C * (κ * r * M * Δ / ℓ ^ 2 +
      (κ * r * M ^ 3 + (κ * r) ^ 2 * M ^ 2 + (κ * r) ^ 3 * M + (κ * r) ^ 4) / ℓ ^ 3) ≤
      κ / 8 * r ^ 2 / ℓ := by
  set T := M * Δ * ℓ + M ^ 3 + κ * r * M ^ 2 + κ ^ 2 * r ^ 2 * M + κ ^ 3 * r ^ 3 with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hT : 8 * (C + 1) * T ≤ r * ℓ ^ 2 := by
    have e1 : 40 * (C + 1) * T = 40 * (C + 1) * (M * Δ * ℓ) + 40 * (C + 1) * M ^ 3 +
        40 * (C + 1) * (κ * r * M ^ 2) + 40 * (C + 1) * ((κ * r) ^ 2 * M) +
        40 * (C + 1) * (κ * r) ^ 3 := by rw [hTdef]; ring
    have h5 : 40 * (C + 1) * T ≤ 5 * (r * ℓ ^ 2) := by
      rw [e1]; linarith only [t1, t2, t3, t4, t5]
    linarith only [h5]
  have hLHS : κ * r * M * Δ / ℓ ^ 2 +
      (κ * r * M ^ 3 + (κ * r) ^ 2 * M ^ 2 + (κ * r) ^ 3 * M + (κ * r) ^ 4) / ℓ ^ 3 =
      κ * r * T / ℓ ^ 3 := by
    rw [hTdef]; field_simp; ring
  rw [hLHS, mul_div_assoc', div_le_div_iff₀ (by positivity) hℓ0]
  have h2 : 8 * (C * T) ≤ r * ℓ ^ 2 := by linarith only [hT, hT0]
  calc C * (κ * r * T) * ℓ = (κ * r * ℓ) * (C * T) := by ring
    _ ≤ (κ * r * ℓ) * (r * ℓ ^ 2 / 8) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith only [h2]
    _ = κ / 8 * r ^ 2 * ℓ ^ 3 := by ring

/-- **The algebra of Lemma `lem:exponents`** in the variables `X = ξ^{1/4800}` and
`L = ℓ_j^{1/8}` (so `ℓ_j = L⁸`, `ξ^{99/100} = X^{4752}`, `ξ^{99/200} = X^{2376}`,
`ξ^{2/3} = X^{3200}`, `ξ^{3/8} = X^{1800}` and `L ≥ X^{225}/2`). -/
theorem exponents_alg {X L R κ cβ C ε : ℝ} (hX0 : 0 < X) (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hLX : X ^ 225 / 2 ≤ L) (hR1 : X ^ 3200 ≤ R) (hR2 : R ≤ 2 * X ^ 2376) (hκ : 0 ≤ κ)
    (hcβ : 0 < cβ) (hC : 0 ≤ C)
    (hs0 : 10000 * X ≤ 1) (hs1 : 240 * 2 ^ 17 * (C + 1) * X ≤ cβ)
    (hs2 : 120 * 2 ^ 16 * κ * (C + 1) * X ≤ 1) (hs3 : 160 * 2 ^ 16 * (C + 1) * κ ^ 2 * cβ * X ≤ 1)
    (hs4 : 160 * 2 ^ 16 * (C + 1) * κ ^ 3 * cβ ^ 2 * X ≤ 1) (hs5 : 256 * κ * cβ * X ≤ ε) :
    3 * X ^ 4752 ≤ L ^ 8 ∧ Real.sqrt 3 * X ^ 2376 ≤ L ^ 8 / 16 ∧
    κ * (cβ * R * L) ≤ ε * L ^ 8 ∧
    C * (κ * (cβ * R * L) * (Real.sqrt 3 * X ^ 2376) * (3 * X ^ 4752) / (L ^ 8) ^ 2 +
      (κ * (cβ * R * L) * (Real.sqrt 3 * X ^ 2376) ^ 3 +
        (κ * (cβ * R * L)) ^ 2 * (Real.sqrt 3 * X ^ 2376) ^ 2 +
        (κ * (cβ * R * L)) ^ 3 * (Real.sqrt 3 * X ^ 2376) + (κ * (cβ * R * L)) ^ 4) / (L ^ 8) ^ 3) ≤
      κ / 8 * (cβ * R * L) ^ 2 / L ^ 8 := by
  have hX1 : X ≤ 1 := by linarith
  have hε0 : 0 ≤ ε := le_trans (by positivity) hs5
  have hpow : ∀ k : ℕ, k ≠ 0 → X ^ k ≤ X := fun k hk => pow_le_of_le_one hX0.le hX1 hk
  have hLn : ∀ n : ℕ, (X ^ 225 / 2) ^ n ≤ L ^ n := fun n =>
    pow_le_pow_left₀ (by positivity) hLX n
  have hs3' : Real.sqrt 3 ≤ 2 := sqrt_three_le_two
  have hs3pos : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hL8 : X ^ 1800 / 256 ≤ L ^ 8 := by
    have := hLn 8
    have e : (X ^ 225 / 2) ^ 8 = X ^ 1800 / 256 := by ring
    rwa [e] at this
  have hX1800 : 0 < X ^ 1800 := by positivity
  -- (i) `Δ ≤ ℓ`
  have hi : 3 * X ^ 4752 ≤ L ^ 8 := by
    have h1 : X ^ 2952 ≤ X := hpow 2952 (by norm_num)
    calc 3 * X ^ 4752 = (3 * X ^ 2952) * X ^ 1800 := by ring
      _ ≤ (1 / 256) * X ^ 1800 := by
          refine mul_le_mul_of_nonneg_right ?_ hX1800.le
          linarith
      _ = X ^ 1800 / 256 := by ring
      _ ≤ L ^ 8 := hL8
  -- (ii) `M ≤ ℓ/16`
  have hii : Real.sqrt 3 * X ^ 2376 ≤ L ^ 8 / 16 := by
    have h1 : X ^ 576 ≤ X := hpow 576 (by norm_num)
    calc Real.sqrt 3 * X ^ 2376 = (Real.sqrt 3 * X ^ 576) * X ^ 1800 := by ring
      _ ≤ (1 / 4096) * X ^ 1800 := by
          refine mul_le_mul_of_nonneg_right ?_ hX1800.le
          calc Real.sqrt 3 * X ^ 576 ≤ 2 * X := mul_le_mul hs3' h1 (by positivity) (by norm_num)
            _ ≤ 1 / 4096 := by linarith
      _ = (X ^ 1800 / 256) / 16 := by ring
      _ ≤ L ^ 8 / 16 := by linarith
  -- (iii) `|c| r ≤ ε ℓ`
  have hiii : κ * (cβ * R * L) ≤ ε * L ^ 8 := by
    have hL7 : X ^ 1575 / 128 ≤ L ^ 7 := by
      have := hLn 7
      have e : (X ^ 225 / 2) ^ 7 = X ^ 1575 / 128 := by ring
      rwa [e] at this
    have h1 : X ^ 801 ≤ X := hpow 801 (by norm_num)
    have h2 : κ * cβ * (2 * X ^ 2376) ≤ ε * L ^ 7 := by
      calc κ * cβ * (2 * X ^ 2376) = (2 * κ * cβ * X ^ 801) * X ^ 1575 := by ring
        _ ≤ (ε / 128) * X ^ 1575 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have h3 : 2 * κ * cβ * X ^ 801 ≤ 2 * κ * cβ * X :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
            linarith
        _ = ε * (X ^ 1575 / 128) := by ring
        _ ≤ ε * L ^ 7 := mul_le_mul_of_nonneg_left hL7 hε0
    calc κ * (cβ * R * L) = κ * cβ * R * L := by ring
      _ ≤ κ * cβ * (2 * X ^ 2376) * L := by
          refine mul_le_mul_of_nonneg_right ?_ hL0.le
          exact mul_le_mul_of_nonneg_left hR2 (by positivity)
      _ ≤ ε * L ^ 7 * L := mul_le_mul_of_nonneg_right h2 hL0.le
      _ = ε * L ^ 8 := by ring
  refine ⟨hi, hii, hiii, ?_⟩
  -- (iv) the error terms of Lemma T
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR1
  obtain ⟨t1, t2⟩ := exponents_t12 hX0 hL0 hL1 hLX hR1 hR2 hcβ hC hs0 hs1
  obtain ⟨t3, t4, t5⟩ := exponents_t345 hX0 hL0 hL1 hLX hR1 hR2 hκ hcβ hC hs0 hs2 hs3 hs4
  exact exponents_err (by positivity) (by positivity) (by positivity) (by positivity) hκ
    t1 t2 t3 t4 t5

/-- `ξ^{n/4800} = (ξ^{1/4800})^n`. -/
theorem rpow_eq_pow_rpow_div {ξ : ℝ} (hξ : 0 ≤ ξ) (n : ℕ) (q : ℝ) (hq : q = n / 4800) :
    ξ ^ q = (ξ ^ (1 / 4800 : ℝ)) ^ n := by
  rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hξ]
  congr 1
  ring

/-- `K X ≤ b` from `X ≤ b/(K+1)`. -/
theorem mul_le_of_le_div_add_one {K b X : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hX : X ≤ b / (K + 1)) : K * X ≤ b := by
  have hK1 : 0 < K + 1 := by linarith
  calc K * X ≤ K * (b / (K + 1)) := mul_le_mul_of_nonneg_left hX hK
    _ ≤ (K + 1) * (b / (K + 1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = b := by field_simp

theorem ell_le_ell {j J : ℕ} (h : j ≤ J) : ell J ≤ ell j := by
  unfold ell
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) h)

/-- **Lemma `lem:exponents`** ((5.8)–(5.9) under Route F; BP2 D10). -/
theorem probe_exponents (C₂ c CR ε : ℝ) (hε : 0 < ε) : ∀ᶠ ξ in 𝓝[>] (0:ℝ),
    ξ ≤ 1/64 ∧ ξ ^ (99/100 : ℝ) ≤ 1/100 ∧
    CR * (Real.sqrt (ell (Jxi ξ) * ξ ^ (99/100 : ℝ)) + ξ ^ (99/100 : ℝ)) ≤ 3/4 * ξ ^ (2/3 : ℝ) ∧
    ∀ j ≤ Jxi ξ, ∀ R, ξ ^ (2/3 : ℝ) ≤ R → R ≤ 2 * ξ ^ (99/200 : ℝ) →
      let r := cBeta * R * ell j ^ (1/8 : ℝ); let Δ := 3 * ξ ^ (99/100 : ℝ)
      let M := Real.sqrt 3 * ξ ^ (99/200 : ℝ)
      Δ ≤ ell j ∧ M ≤ ell j / 16 ∧ |c| * r ≤ ε * ell j ∧
      1 + Real.log (ell j)⁻¹ ≤ 2 * Real.log ξ⁻¹ ∧
      C₂ * (|c| * r * M * Δ / ell j ^ 2 + (|c| * r * M ^ 3 + (c * r) ^ 2 * M ^ 2 +
        (|c| * r) ^ 3 * M + (c * r) ^ 4) / ell j ^ 3) ≤ |c| / 8 * r ^ 2 / ell j := by
  set κ := |c| with hκdef
  set C := max C₂ 0 with hCdef
  have hκ : 0 ≤ κ := abs_nonneg c
  have hC : 0 ≤ C := le_max_right _ _
  have hcβ : 0 < cBeta := cBeta_pos
  -- the constants of the smallness conditions
  set K₁ := 240 * 2 ^ 17 * (C + 1) with hK₁
  set K₂ := 120 * 2 ^ 16 * κ * (C + 1) with hK₂
  set K₃ := 160 * 2 ^ 16 * (C + 1) * κ ^ 2 * cBeta with hK₃
  set K₄ := 160 * 2 ^ 16 * (C + 1) * κ ^ 3 * cBeta ^ 2 with hK₄
  set K₅ := 256 * κ * cBeta with hK₅
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hK₃0 : 0 ≤ K₃ := by positivity
  have hK₄0 : 0 ≤ K₄ := by positivity
  have hK₅0 : 0 ≤ K₅ := by positivity
  set X₀ := min (1 / 10000) (min (cBeta / (K₁ + 1)) (min (1 / (K₂ + 1)) (min (1 / (K₃ + 1))
    (min (1 / (K₄ + 1)) (min (ε / (K₅ + 1)) (3 / 8 / (|CR| + 1))))))) with hX₀def
  have hX₀ : 0 < X₀ := by
    simp only [hX₀def, lt_min_iff]
    refine ⟨by norm_num, by positivity, by positivity, by positivity, by positivity,
      by positivity, by positivity⟩
  have hδ : 0 < min (1 / 64) (X₀ ^ 4800) := lt_min (by norm_num) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ξ hξ
  obtain ⟨hξ0, hξδ⟩ := hξ
  have hξ64 : ξ ≤ 1 / 64 := hξδ.le.trans (min_le_left _ _)
  have hξ1 : ξ ≤ 1 := by linarith
  set X := ξ ^ (1 / 4800 : ℝ) with hXdef
  have hX0 : 0 < X := Real.rpow_pos_of_pos hξ0 _
  have hXX₀ : X ≤ X₀ := by
    have h1 : ξ ≤ X₀ ^ 4800 := hξδ.le.trans (min_le_right _ _)
    have h2 : X ≤ (X₀ ^ 4800) ^ (1 / 4800 : ℝ) :=
      Real.rpow_le_rpow hξ0.le h1 (by norm_num)
    have h3 : (X₀ ^ 4800) ^ (1 / 4800 : ℝ) = X₀ := by
      have := Real.pow_rpow_inv_natCast hX₀.le (show (4800 : ℕ) ≠ 0 by norm_num)
      rw [show ((4800 : ℕ) : ℝ)⁻¹ = (1 / 4800 : ℝ) by norm_num] at this
      exact this
    rwa [h3] at h2
  -- the smallness conditions
  have hs0 : 10000 * X ≤ 1 := by
    have := hXX₀.trans (min_le_left _ _)
    linarith
  have hX₀1 : X₀ ≤ cBeta / (K₁ + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hX₀2 : X₀ ≤ 1 / (K₂ + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hX₀3 : X₀ ≤ 1 / (K₃ + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have hX₀4 : X₀ ≤ 1 / (K₄ + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hX₀5 : X₀ ≤ ε / (K₅ + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hX₀6 : X₀ ≤ 3 / 8 / (|CR| + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hs1 : K₁ * X ≤ cBeta := mul_le_of_le_div_add_one hK₁0 hcβ.le (hXX₀.trans hX₀1)
  have hs2 : K₂ * X ≤ 1 := mul_le_of_le_div_add_one hK₂0 zero_le_one (hXX₀.trans hX₀2)
  have hs3 : K₃ * X ≤ 1 := mul_le_of_le_div_add_one hK₃0 zero_le_one (hXX₀.trans hX₀3)
  have hs4 : K₄ * X ≤ 1 := mul_le_of_le_div_add_one hK₄0 zero_le_one (hXX₀.trans hX₀4)
  have hs5 : K₅ * X ≤ ε := mul_le_of_le_div_add_one hK₅0 hε.le (hXX₀.trans hX₀5)
  have hs6 : |CR| * X ≤ 3 / 8 :=
    mul_le_of_le_div_add_one (abs_nonneg _) (by norm_num) (hXX₀.trans hX₀6)
  -- the powers of `ξ`
  have hpa : ξ ^ (99 / 100 : ℝ) = X ^ 4752 := rpow_eq_pow_rpow_div hξ0.le 4752 _ (by norm_num)
  have hpa2 : ξ ^ (99 / 200 : ℝ) = X ^ 2376 := rpow_eq_pow_rpow_div hξ0.le 2376 _ (by norm_num)
  have hpδ : ξ ^ (2 / 3 : ℝ) = X ^ 3200 := rpow_eq_pow_rpow_div hξ0.le 3200 _ (by norm_num)
  have hp38 : ξ ^ (3 / 8 : ℝ) = X ^ 1800 := rpow_eq_pow_rpow_div hξ0.le 1800 _ (by norm_num)
  have hp19 : ξ ^ (19 / 1200 : ℝ) = X ^ 76 := rpow_eq_pow_rpow_div hξ0.le 76 _ (by norm_num)
  have hX1 : X ≤ 1 := by linarith
  have hpow : ∀ k : ℕ, k ≠ 0 → X ^ k ≤ X := fun k hk => pow_le_of_le_one hX0.le hX1 hk
  refine ⟨hξ64, ?_, ?_, ?_⟩
  · -- (X1)
    rw [hpa]
    have := hpow 4752 (by norm_num)
    linarith
  · -- (X5)
    have hS := sqrt_ell_Jxi_mul_add_le hξ0 hξ1 (by positivity) (le_refl (ξ ^ (99 / 100 : ℝ)))
    have hS0 : 0 ≤ Real.sqrt (ell (Jxi ξ) * ξ ^ (99 / 100 : ℝ)) + ξ ^ (99 / 100 : ℝ) := by
      positivity
    have h76 : X ^ 76 ≤ X := hpow 76 (by norm_num)
    have hδ0 : 0 ≤ ξ ^ (2 / 3 : ℝ) := by positivity
    calc CR * (Real.sqrt (ell (Jxi ξ) * ξ ^ (99 / 100 : ℝ)) + ξ ^ (99 / 100 : ℝ))
        ≤ |CR| * (Real.sqrt (ell (Jxi ξ) * ξ ^ (99 / 100 : ℝ)) + ξ ^ (99 / 100 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self CR) hS0
      _ ≤ |CR| * (2 * ξ ^ (19 / 1200 : ℝ) * ξ ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hS (abs_nonneg _)
      _ = 2 * (|CR| * X ^ 76) * ξ ^ (2 / 3 : ℝ) := by rw [hp19]; ring
      _ ≤ 2 * (|CR| * X) * ξ ^ (2 / 3 : ℝ) := by
          gcongr
      _ ≤ 2 * (3 / 8) * ξ ^ (2 / 3 : ℝ) := by gcongr
      _ = 3 / 4 * ξ ^ (2 / 3 : ℝ) := by ring
  · -- the levels `j ≤ J`
    intro j hj R hR1 hR2
    dsimp only
    have hℓ := ell_pos j
    set L := ell j ^ (1 / 8 : ℝ) with hLdef
    have hL0 : 0 < L := Real.rpow_pos_of_pos hℓ _
    have hL1 : L ≤ 1 := Real.rpow_le_one hℓ.le (ell_le_one j) (by norm_num)
    have hL8 : L ^ 8 = ell j := by
      rw [hLdef, ← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]
      norm_num
    have hLX : X ^ 225 / 2 ≤ L := by
      have h1 : X ^ 1800 / 2 < ell j := by
        have := (ell_Jxi_bounds hξ0 hξ1).1
        rw [hp38] at this
        exact this.trans_le (ell_le_ell hj)
      have h2 : (X ^ 225 / 2) ^ 8 ≤ L ^ 8 := by
        rw [hL8]
        have e : (X ^ 225 / 2) ^ 8 = X ^ 1800 / 256 := by ring
        rw [e]
        have : 0 ≤ X ^ 1800 := by positivity
        linarith
      exact (pow_le_pow_iff_left₀ (by positivity) hL0.le (by norm_num)).1 h2
    rw [hpδ] at hR1
    rw [hpa2] at hR2
    obtain ⟨hi, hii, hiii, hiv⟩ := exponents_alg (κ := κ) (C := C) (ε := ε) hX0 hL0 hL1 hLX hR1
      hR2 hκ hcβ hC hs0 hs1 hs2 hs3 hs4 hs5
    rw [hpa, hpa2, ← hL8]
    refine ⟨hi, hii, hiii, ?_, ?_⟩
    · rw [hL8]
      exact (log_inv_ell_le hξ0 (by linarith) hj).2
    · have key2 : ∀ x : ℝ, (c * x) ^ 2 = (|c| * x) ^ 2 := fun x => by
        rw [mul_pow, mul_pow, sq_abs]
      have key4 : ∀ x : ℝ, (c * x) ^ 4 = (|c| * x) ^ 4 := fun x => by
        rw [mul_pow, mul_pow, Even.pow_abs ⟨2, by norm_num⟩]
      have hc2 : (c * (cBeta * R * L)) ^ 2 = (κ * (cBeta * R * L)) ^ 2 := key2 _
      have hc4 : (c * (cBeta * R * L)) ^ 4 = (κ * (cBeta * R * L)) ^ 4 := key4 _
      rw [hc2, hc4]
      have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR1
      have hS0 : 0 ≤ κ * (cBeta * R * L) * (Real.sqrt 3 * X ^ 2376) * (3 * X ^ 4752) /
          (L ^ 8) ^ 2 + (κ * (cBeta * R * L) * (Real.sqrt 3 * X ^ 2376) ^ 3 +
          (κ * (cBeta * R * L)) ^ 2 * (Real.sqrt 3 * X ^ 2376) ^ 2 +
          (κ * (cBeta * R * L)) ^ 3 * (Real.sqrt 3 * X ^ 2376) + (κ * (cBeta * R * L)) ^ 4) /
          (L ^ 8) ^ 3 := by positivity
      exact (mul_le_mul_of_nonneg_right (le_max_left C₂ 0) hS0).trans hiv

end SmallGammaGeodesics
