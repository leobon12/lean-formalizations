import HigherDimLQGMetric.DGZ.BadBoxRecursion

/-!
# DGZ Lemma 5.9: the events `𝒥₁` and `𝒥₂′` are likely (packet L4a2)

Source: [2] Lemma 5.9 (TeX l. 2365–2389, p. 45); planning audit MA7 D-5.5–5.9 (Lemma 5.9:
"`P[𝒥₁ᶜ] ≤ C2^{dn-(α+d)a_m} ≤ C2^{-n/C}` since `λ < α/(2(α+d))` and `a_m ≥ (1-2λ)n`;
`𝒥₂′` by D-OSC"),
G9; blueprint Lemma `r2:lem:59` and `r2:lem:oscconds`(c).

The top level is `m = dgzLevel λ K n` (DGZ (5.5)). For `n ≥ n₀(K)` (`BadBox.dgzLevel_facts`):
`1 ≤ m`, `a_m ≤ n` and `(1 - 2λ)n ≤ a_m` (L4a1's `dgzLevel_spec`, `dgzLevel_lower`); for smaller
`n` the bounds below are at least `1`.

* `prob_J2'_compl_le` (`𝒥₂′`; blueprint `r2:lem:oscconds`(c)): `P[(𝒥₂′)ᶜ] ≤ C 2^{-n}` for `K ≥ K₀`,
  from `prob_not_eventJ2'_le_card` (at most `(m+1)(7·2^n)^d` boxes, slope `K√a_m/8`) and
  `a_m ≥ n/2`.
* `prob_J1_compl_le` (`𝒥₁`): the `a_m`-boxes contained in `B₂(0)` are the boxes `B_{s_m}(s_m u)`
  with `|u|_∞ ≤ 2/s_m - 1`, at most `2^{d(n - a_m + 2)}`; by Lemma 5.8 (`q_le`)
  `P[𝒥₁ᶜ] ≤ 2^{d(n-a_m+2)} 2^{-α a_m} ≤ 4^d 2^{-αn/2}`, since `(d + α)(1 - 2λ) = d + α/2` for
  `λ = α/(4(α + d))`.
* `prob_J_compl_le` (**target**, Lemma 5.9): `P[(𝒥₁ ∩ 𝒥₂′)ᶜ] ≤ C 2^{-n/C}` for all `n, k`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## The top level -/

namespace BadBox

/-- For `0 < λ ≤ 1/4` and `K ≥ 1` there is `n₀` such that for `n ≥ n₀` the top level
`m = dgzLevel λ K n` satisfies `1 ≤ m`, `a_m ≤ n` and `(1 - 2λ) n ≤ a_m` (DGZ (5.5), (5.6)). -/
theorem dgzLevel_facts {lam : ℝ} (hlam0 : 0 < lam) (hlam4 : lam ≤ 1 / 4) {K : ℕ} (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      1 ≤ dgzLevel lam K n ∧ dgzSeq lam K (dgzLevel lam K n) ≤ n ∧
        (1 - 2 * lam) * n ≤ dgzSeq lam K (dgzLevel lam K n) := by
  have h1l : 0 < 1 - lam := by linarith
  refine ⟨⌈((K ^ 4 : ℕ) : ℝ) / (1 - lam)⌉₊ + ⌈1 / (2 * lam ^ 2)⌉₊, fun n hn => ?_⟩
  have hn1 : ((K ^ 4 : ℕ) : ℝ) / (1 - lam) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_add_right _ _).trans hn)
  have hn2 : 1 / (2 * lam ^ 2) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_add_left _ _).trans hn)
  have hK4 : ((K ^ 4 : ℕ) : ℝ) ≤ (1 - lam) * n := by
    rw [div_le_iff₀ h1l] at hn1
    linarith
  have hl2 : 1 ≤ 2 * lam ^ 2 * n := by
    rw [div_le_iff₀ (by positivity)] at hn2
    linarith
  obtain ⟨hm1, hmn, -⟩ := dgzLevel_spec hlam0.le hK hK4
  refine ⟨hm1, ?_, dgzLevel_lower hlam0.le hK hK4 hl2⟩
  have : (dgzSeq lam K (dgzLevel lam K n) : ℝ) ≤ n := by
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  exact_mod_cast this

/-! ## `𝒥₂′` -/

/-- The arithmetic of `𝒥₂′`: `(m+1)(7·2^n)^d · 2e^{-(K√M/8 - C)²/C} ≤ 2·7^d·2^{-n}` when
`K ≥ 16C`, `K² ≥ 512C(d+2)`, `M ≥ K⁴`, `n ≤ 2M` and `m ≤ n`. -/
theorem j2_arith {C : ℝ} (hC : 0 < C) (d : ℕ) {K : ℝ} (hK1 : 1 ≤ K) (hK16 : 16 * C ≤ K)
    (hKK : 512 * C * (d + 2) ≤ K ^ 2) {n m M : ℕ} (hM : K ^ 4 ≤ M) (hMn : (n : ℝ) ≤ 2 * M)
    (hm : m ≤ n) :
    ((m : ℝ) + 1) * ((7 : ℝ) * 2 ^ n) ^ d * (2 * Real.exp (-(K * √(M : ℝ) / 8 - C) ^ 2 / C)) ≤
      2 * 7 ^ d * (2 : ℝ) ^ (-(n : ℝ)) := by
  have hK0 : 0 < K := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK1
  have hsq : K ^ 2 ≤ √(M : ℝ) := by
    rw [Real.le_sqrt (by positivity) hM0]
    calc (K ^ 2) ^ 2 = K ^ 4 := by ring
      _ ≤ (M : ℝ) := hM
  have hsqM : √(M : ℝ) ^ 2 = M := Real.sq_sqrt hM0
  have hx : 2 * C ≤ K * √(M : ℝ) / 8 := by
    have h1 : K ≤ K * √(M : ℝ) := by
      calc K = K * 1 := (mul_one K).symm
        _ ≤ K * √(M : ℝ) := mul_le_mul_of_nonneg_left (hK2.trans hsq) hK0.le
    linarith
  have hsq2 : K ^ 2 * M / 256 ≤ (K * √(M : ℝ) / 8 - C) ^ 2 := by
    have h1 : K * √(M : ℝ) / 16 ≤ K * √(M : ℝ) / 8 - C := by linarith
    have h2 : 0 ≤ K * √(M : ℝ) / 16 := by positivity
    calc K ^ 2 * M / 256 = (K * √(M : ℝ) / 16) ^ 2 := by
          rw [mul_div_assoc, div_pow, mul_pow, hsqM]
          ring
      _ ≤ (K * √(M : ℝ) / 8 - C) ^ 2 := pow_le_pow_left₀ h2 h1 2
  have hexp1 : Real.exp (-(K * √(M : ℝ) / 8 - C) ^ 2 / C) ≤ Real.exp (-((d + 2) * n)) := by
    rw [Real.exp_le_exp, neg_div, neg_le_neg_iff, le_div_iff₀ hC]
    have h1 : K ^ 2 * n / 512 ≤ K ^ 2 * M / 256 := by nlinarith
    have h2 : 512 * C * (d + 2) * n ≤ K ^ 2 * n := mul_le_mul_of_nonneg_right hKK hn0
    nlinarith
  have hm1 : (m : ℝ) + 1 ≤ Real.exp n := by
    have : (m : ℝ) ≤ n := by exact_mod_cast hm
    have := Real.add_one_le_exp (n : ℝ)
    linarith
  have h7 : ((7 : ℝ) * 2 ^ n) ^ d ≤ 7 ^ d * Real.exp (d * n) := by
    rw [mul_pow]
    have h2 : (2 : ℝ) ^ n ≤ Real.exp n := BadBox.two_pow_le_exp n
    have h3 : ((2 : ℝ) ^ n) ^ d ≤ Real.exp n ^ d := pow_le_pow_left₀ (by positivity) h2 d
    rw [← Real.exp_nat_mul] at h3
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hfin : Real.exp (-(n : ℝ)) ≤ (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_def_of_pos two_pos, Real.exp_le_exp]
    obtain ⟨-, hl1⟩ := log_two_pos_lt_one
    nlinarith
  calc ((m : ℝ) + 1) * ((7 : ℝ) * 2 ^ n) ^ d * (2 * Real.exp (-(K * √(M : ℝ) / 8 - C) ^ 2 / C))
      ≤ Real.exp n * (7 ^ d * Real.exp (d * n)) * (2 * Real.exp (-((d + 2) * n))) := by
        gcongr
    _ = 2 * 7 ^ d * Real.exp (-(n : ℝ)) := by
        rw [show 2 * 7 ^ d * Real.exp (-(n : ℝ)) =
          2 * 7 ^ d * Real.exp (n + d * n + -((d + 2) * n)) by ring_nf]
        rw [Real.exp_add, Real.exp_add]
        ring
    _ ≤ 2 * 7 ^ d * (2 : ℝ) ^ (-(n : ℝ)) := by gcongr

end BadBox

/-- **`𝒥₂′` is likely** (MA7 D-OSC; blueprint `r2:lem:oscconds`(c); DGZ Lemma 5.9, second half):
there is `K₀` such that for every `K ≥ K₀` there is `C` with `P[(𝒥₂′)ᶜ] ≤ C 2^{-n}` for every dyadic
realization and all parameters with DGZ's sequence (`m = dgzLevel λ K n`). -/
theorem prob_J2'_compl_le {κ : Rd d → ℝ} {Q : ℝ} (hκ : IsLFPPKernel κ) (hQ : √(2 * d) < Q) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∃ C > 0,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.K = K → p.a = dgzSeq (dgzLambda d Q) K →
          P {ω | ¬ EventJ2' p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n)} ≤
            ENNReal.ofReal (C * (2 : ℝ) ^ (-(p.n : ℝ))) := by
  have hα := dgzAlpha_pos hQ
  have hlam : 0 < dgzLambda d Q := dgzLambda_pos hα
  have hlam4 : dgzLambda d Q ≤ 1 / 4 := dgzLambda_le_quarter hα
  set lam := dgzLambda d Q with hlamdef
  obtain ⟨C₀, hC₀, hcard⟩ := prob_not_eventJ2'_le_card (d := d) hκ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨⌈16 * C₀ + 512 * C₀ * (d + 2) + 1⌉₊, fun K hK => ?_⟩
  have hKr : 16 * C₀ + 512 * C₀ * (d + 2) + 1 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hK)
  have hX : 0 ≤ 512 * C₀ * ((d : ℝ) + 2) := by positivity
  have hK1r : (1 : ℝ) ≤ K := by linarith
  have hK1 : 1 ≤ K := by exact_mod_cast hK1r
  have hK16 : 16 * C₀ ≤ (K : ℝ) := by linarith
  have hKK : 512 * C₀ * (d + 2) ≤ (K : ℝ) ^ 2 := by nlinarith
  obtain ⟨n₀, hn₀⟩ := BadBox.dgzLevel_facts hlam hlam4 hK1
  refine ⟨2 * 7 ^ d + 2 ^ n₀, by positivity, fun Ω _ P W H hH p hpK ha => ?_⟩
  have := hH.whiteNoise.isProbabilityMeasure
  have hmono : Monotone p.a := by rw [ha]; exact dgzSeq_monotone hlam.le hK1
  rcases lt_or_ge p.n n₀ with hn | hn
  · -- small `n`: the bound is at least `1`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 : ℝ) ≤ 2 ^ n₀ * (2 : ℝ) ^ (-(p.n : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add two_pos]
      apply Real.one_le_rpow one_le_two
      have : (p.n : ℝ) ≤ n₀ := by exact_mod_cast hn.le
      linarith
    have h2 : 0 ≤ 2 * 7 ^ d * (2 : ℝ) ^ (-(p.n : ℝ)) := by positivity
    nlinarith
  · obtain ⟨hm1, hmn, hlow⟩ := hn₀ p.n hn
    set m := dgzLevel lam K p.n with hm
    have hamn : p.a m ≤ p.n := by rw [ha]; exact hmn
    have hM : (K : ℝ) ^ 4 ≤ p.a m := by
      have : K ^ 4 ≤ p.a m := by rw [ha]; exact pow_le_dgzSeq hlam.le hK1 hm1
      exact_mod_cast this
    have hMn : (p.n : ℝ) ≤ 2 * p.a m := by
      rw [ha]
      nlinarith
    have hmn' : m ≤ p.n := by
      have : m ≤ p.a m := by rw [ha]; exact le_dgzSeq hlam.le hK1 m
      omega
    have hT : C₀ ≤ p.K * √(p.a m : ℝ) / 8 := by
      rw [hpK]
      have hsq : (K : ℝ) ^ 2 ≤ √(p.a m : ℝ) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        calc ((K : ℝ) ^ 2) ^ 2 = (K : ℝ) ^ 4 := by ring
          _ ≤ _ := hM
      have h1 : (K : ℝ) ≤ K * √(p.a m : ℝ) := by
        calc (K : ℝ) = K * 1 := (mul_one _).symm
          _ ≤ K * √(p.a m : ℝ) :=
            mul_le_mul_of_nonneg_left ((one_le_pow₀ hK1r).trans hsq) (by positivity)
      linarith
    refine (hcard Ω P W H hH p hmono m hamn hT).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hpK]
    calc ((m : ℝ) + 1) * ((7 : ℝ) * 2 ^ p.n) ^ d *
          (2 * Real.exp (-(K * √(p.a m : ℝ) / 8 - C₀) ^ 2 / C₀))
        ≤ 2 * 7 ^ d * (2 : ℝ) ^ (-(p.n : ℝ)) := BadBox.j2_arith hC₀ d hK1r hK16 hKK hM hMn hmn'
      _ ≤ (2 * 7 ^ d + 2 ^ n₀) * (2 : ℝ) ^ (-(p.n : ℝ)) := by
          gcongr
          have : (0 : ℝ) ≤ 2 ^ n₀ := by positivity
          linarith

/-! ## `𝒥₁` -/

namespace BadBox

/-- The `a_m`-boxes contained in `B₂(0)`: `B_{s_m}(s_m u) ⊆ B₂(0)` forces `|u|_∞ ≤ 2/s_m - 1 =
2^{n - a_m + 1} - 1`. -/
theorem mem_cube_of_obox_subset_two (p : NiceParams) (m : ℕ) (u : Zd d)
    (h : obox (latPt (p.s m) u) (p.s m) ⊆ obox (0 : Rd d) 2) :
    u ∈ BadBox.cube 0 (2 ^ (p.n - p.a m + 1) - 1) := by
  set N : ℕ := 2 ^ (p.n - p.a m + 1) with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNs : (N : ℝ) * p.s m = 2 := by
    rw [mul_comm]
    exact p.s_mul_two_pow m
  have e : obox (0 : Rd d) 2 = obox (latPt ((N : ℝ) * p.s m) 0) ((N : ℝ) * p.s m) := by
    rw [HigherDimLFPP.DGZ.latPt_zero, hNs]
  rw [e] at h
  have := (BadBox.obox_subset_iff_mem_cube (p.s_pos m) N hN1 0 u).1 h
  rwa [smul_zero] at this

end BadBox

/-- **`𝒥₁` is likely** (DGZ Lemma 5.9, first half; MA7 D-5.5–5.9): for `R ≥ 2ρ + 10` there is
`θ₀ > 0` such that for every `θ ∈ (0, θ₀]` there is `K₀` such that for every `K ≥ K₀` there is `C`
such that for every `ε > 0` there is `L₀` with `P[𝒥₁ᶜ] ≤ C 2^{-αn/2}` for every dyadic realization,
DGZ's parameters with `L ≥ L₀` and all `n, k` (`m = dgzLevel λ K n`). -/
theorem prob_J1_compl_le {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ} (hR : 2 * ρ + 10 ≤ (R : ℝ)) :
    ∃ θ₀ > 0, ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∃ C > 0, ∀ ε : ℝ, 0 < ε →
      ∃ L₀ : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.ε = ε → p.R = R → p.K = K →
          L₀ ≤ p.L → p.a = dgzSeq (dgzLambda d Q) K →
            P {ω | ¬ EventJ1 p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n)} ≤
              ENNReal.ofReal (C * (2 : ℝ) ^ (-(dgzAlpha d Q * p.n / 2))) := by
  have hα := dgzAlpha_pos h.subcritical
  have hlam : 0 < dgzLambda d Q := dgzLambda_pos hα
  have hlam4 : dgzLambda d Q ≤ 1 / 4 := dgzLambda_le_quarter hα
  have hlamdef : dgzLambda d Q = dgzAlpha d Q / (4 * (dgzAlpha d Q + d)) := rfl
  set α := dgzAlpha d Q with hαdef
  set lam := dgzLambda d Q with hlamdef'
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- `(d + α)(1 - 2λ) = d + α/2`
  have hkey : ((d : ℝ) + α) * (1 - 2 * lam) = d + α / 2 := by
    rw [hlamdef]
    field_simp
    ring
  obtain ⟨θ₀, hθ₀, hq⟩ := q_le h hρ hR
  refine ⟨θ₀, hθ₀, fun θ hθ hθθ₀ => ?_⟩
  obtain ⟨K₀, hK₀⟩ := hq θ hθ hθθ₀
  refine ⟨max K₀ 1, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := (le_max_right _ _).trans hK
  obtain ⟨n₀, hn₀⟩ := BadBox.dgzLevel_facts hlam hlam4 hK1
  refine ⟨4 ^ d + (2 : ℝ) ^ (α * n₀ / 2), by positivity, fun ε hε => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hK₀ K ((le_max_left _ _).trans hK) ε hε
  refine ⟨L₀, fun Ω _ P W H hH p hpξ hpQ hpθ hpε hpR hpK hL ha => ?_⟩
  have := hH.whiteNoise.isProbabilityMeasure
  rcases lt_or_ge p.n n₀ with hn | hn
  · -- small `n`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (α * n₀ / 2) * (2 : ℝ) ^ (-(α * p.n / 2)) := by
      rw [← Real.rpow_add two_pos]
      apply Real.one_le_rpow one_le_two
      have : (p.n : ℝ) ≤ n₀ := by exact_mod_cast hn.le
      nlinarith
    have h2 : 0 ≤ (4 : ℝ) ^ d * (2 : ℝ) ^ (-(α * p.n / 2)) := by positivity
    nlinarith
  · obtain ⟨hm1, hmn, hlow⟩ := hn₀ p.n hn
    set m := dgzLevel lam K p.n with hm
    have hamn : p.a m ≤ p.n := by rw [ha]; exact hmn
    have hlow' : (1 - 2 * lam) * p.n ≤ p.a m := by rw [ha]; exact hlow
    -- the union bound
    have hset : {ω | ¬ EventJ1 p (fun q z => H q z ω) m} =
        {ω | ∃ u : Zd d, obox (latPt (p.s m) u) (p.s m) ⊆ obox (0 : Rd d) 2 ∧
          ¬ NiceBox p (fun q z => H q z ω) m u} := by
      ext ω
      simp only [mem_ofPred_eq, EventJ1, not_forall, exists_prop]
    rw [hset]
    refine (BadBox.measure_exists_le_card_mul P (BadBox.cube 0 (2 ^ (p.n - p.a m + 1) - 1)) _ _
      (fun u hu => BadBox.mem_cube_of_obox_subset_two p m u hu)
      (b := ENNReal.ofReal ((2 : ℝ) ^ (-(α * p.a m)))) fun u _ =>
        hL₀ Ω P W H hH p hpξ hpQ hpθ hpε hpR hpK hL ha m hm1 hamn u).trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [BadBox.card_cube]
    -- `(2N - 1)^d 2^{-α a_m} ≤ 4^d 2^{-αn/2}`
    set e : ℕ := p.n - p.a m with he
    have hcard : (((2 * (2 ^ (e + 1) - 1) + 1) ^ d : ℕ) : ℝ) ≤ ((2 : ℝ) ^ ((e : ℝ) + 2)) ^ d := by
      have h1 : 2 * (2 ^ (e + 1) - 1) + 1 ≤ 2 ^ (e + 2) := by
        have : 1 ≤ 2 ^ (e + 1) := Nat.one_le_two_pow
        rw [pow_succ 2 (e + 1)]
        omega
      have h2 : ((2 * (2 ^ (e + 1) - 1) + 1) ^ d : ℕ) ≤ (2 ^ (e + 2)) ^ d :=
        Nat.pow_le_pow_left h1 d
      have h3 : (((2 ^ (e + 2)) ^ d : ℕ) : ℝ) = ((2 : ℝ) ^ ((e : ℝ) + 2)) ^ d := by
        push_cast
        rw [← Real.rpow_natCast 2 (e + 2)]
        push_cast
        rfl
      rw [← h3]
      exact_mod_cast h2
    have he' : (e : ℝ) = p.n - p.a m := by rw [he, Nat.cast_sub hamn]
    calc (((2 * (2 ^ (e + 1) - 1) + 1) ^ d : ℕ) : ℝ) * (2 : ℝ) ^ (-(α * p.a m))
        ≤ ((2 : ℝ) ^ ((e : ℝ) + 2)) ^ d * (2 : ℝ) ^ (-(α * p.a m)) := by gcongr
      _ = (2 : ℝ) ^ ((d : ℝ) * ((e : ℝ) + 2) + -(α * p.a m)) := by
          rw [BadBox.two_rpow_pow, ← Real.rpow_add two_pos]
      _ ≤ (2 : ℝ) ^ (2 * (d : ℝ) + -(α * p.n / 2)) := by
          apply Real.rpow_le_rpow_of_exponent_le one_le_two
          rw [he']
          have h1 : ((d : ℝ) + α) * ((1 - 2 * lam) * p.n) ≤ ((d : ℝ) + α) * p.a m :=
            mul_le_mul_of_nonneg_left hlow' (by positivity)
          rw [← mul_assoc, hkey] at h1
          nlinarith
      _ = 4 ^ d * (2 : ℝ) ^ (-(α * p.n / 2)) := by
          rw [Real.rpow_add two_pos]
          congr 1
          rw [show (2 : ℝ) * d = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
            pow_mul]
          norm_num
      _ ≤ (4 ^ d + (2 : ℝ) ^ (α * n₀ / 2)) * (2 : ℝ) ^ (-(α * p.n / 2)) := by
          gcongr
          have : (0 : ℝ) ≤ (2 : ℝ) ^ (α * n₀ / 2) := by positivity
          linarith

/-! ## Lemma 5.9 -/

/-- **DGZ Lemma 5.9** (target `prob_J_compl_le`; MA7 D-5.5–5.9, G9; blueprint `r2:lem:59`): for
`R ≥ 2ρ + 10` (`ρ` a support radius of `κ`) there is `θ₀ > 0` such that for every `θ ∈ (0, θ₀]`
there is `K₀` such that for every `K ≥ K₀` there is `C > 0` such that for every `ε > 0` there is
`L₀` with `P[(𝒥₁ ∩ 𝒥₂′)ᶜ] ≤ C 2^{-n/C}` for every dyadic realization, DGZ's parameters (`ξ, Q, θ,
ε, R, K` fixed, `L ≥ L₀`, `a = dgzSeq λ K`) and all `n, k`, with `m = dgzLevel λ K n`. -/
theorem prob_J_compl_le {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ} (hR : 2 * ρ + 10 ≤ (R : ℝ)) :
    ∃ θ₀ > 0, ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∃ C > 0, ∀ ε : ℝ, 0 < ε →
      ∃ L₀ : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.ε = ε → p.R = R → p.K = K →
          L₀ ≤ p.L → p.a = dgzSeq (dgzLambda d Q) K →
            P {ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n) ∧
              EventJ2' p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n))} ≤
              ENNReal.ofReal (C * (2 : ℝ) ^ (-(p.n : ℝ) / C)) := by
  have hα := dgzAlpha_pos h.subcritical
  obtain ⟨θ₀, hθ₀, hJ1⟩ := prob_J1_compl_le h hρ hR
  obtain ⟨K₂, hJ2⟩ := prob_J2'_compl_le (Q := Q) h.kernel h.subcritical
  refine ⟨θ₀, hθ₀, fun θ hθ hθθ₀ => ?_⟩
  obtain ⟨K₁, hK₁⟩ := hJ1 θ hθ hθθ₀
  refine ⟨max K₁ K₂, fun K hK => ?_⟩
  obtain ⟨C₁, hC₁, hJ1K⟩ := hK₁ K ((le_max_left _ _).trans hK)
  obtain ⟨C₂, hC₂, hJ2K⟩ := hJ2 K ((le_max_right _ _).trans hK)
  set C : ℝ := max (C₁ + C₂) (max (2 / dgzAlpha d Q) 1) with hC
  have hC1 : 1 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC0 : 0 < C := by linarith
  have hCα : 2 / dgzAlpha d Q ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCC : C₁ + C₂ ≤ C := le_max_left _ _
  refine ⟨C, hC0, fun ε hε => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hJ1K ε hε
  refine ⟨L₀, fun Ω _ P W H hH p hpξ hpQ hpθ hpε hpR hpK hL ha => ?_⟩
  have h1 := hL₀ Ω P W H hH p hpξ hpQ hpθ hpε hpR hpK hL ha
  have h2 := hJ2K Ω P W H hH p hpK ha
  have hsub : {ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n) ∧
      EventJ2' p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n))} ⊆
      {ω | ¬ EventJ1 p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n)} ∪
        {ω | ¬ EventJ2' p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n)} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union, not_and_or] at hω ⊢
    exact hω
  have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hr1 : (2 : ℝ) ^ (-(dgzAlpha d Q * p.n / 2)) ≤ (2 : ℝ) ^ (-(p.n : ℝ) / C) := by
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have h3 : (p.n : ℝ) / C ≤ dgzAlpha d Q * p.n / 2 := by
      rw [div_le_iff₀ hC0]
      have h4 : 2 ≤ dgzAlpha d Q * C := by
        rw [div_le_iff₀ hα] at hCα
        linarith
      nlinarith
    rw [neg_div]
    linarith
  have hr2 : (2 : ℝ) ^ (-(p.n : ℝ)) ≤ (2 : ℝ) ^ (-(p.n : ℝ) / C) := by
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hC0]
    nlinarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ (-(dgzAlpha d Q * p.n / 2))) +
        ENNReal.ofReal (C₂ * (2 : ℝ) ^ (-(p.n : ℝ))) :=
        (measure_union_le _ _).trans (add_le_add h1 h2)
    _ = ENNReal.ofReal (C₁ * (2 : ℝ) ^ (-(dgzAlpha d Q * p.n / 2)) +
        C₂ * (2 : ℝ) ^ (-(p.n : ℝ))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(p.n : ℝ) / C)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hy : (0 : ℝ) ≤ (2 : ℝ) ^ (-(p.n : ℝ) / C) := by positivity
        calc C₁ * (2 : ℝ) ^ (-(dgzAlpha d Q * p.n / 2)) + C₂ * (2 : ℝ) ^ (-(p.n : ℝ))
            ≤ C₁ * (2 : ℝ) ^ (-(p.n : ℝ) / C) + C₂ * (2 : ℝ) ^ (-(p.n : ℝ) / C) := by
              gcongr
          _ = (C₁ + C₂) * (2 : ℝ) ^ (-(p.n : ℝ) / C) := by ring
          _ ≤ C * (2 : ℝ) ^ (-(p.n : ℝ) / C) := mul_le_mul_of_nonneg_right hCC hy

end DGZ

end HigherDimLQGMetric
