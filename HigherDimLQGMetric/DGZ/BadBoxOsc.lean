import HigherDimLQGMetric.DGZ.BadBoxArith

/-!
# DGZ §5.2: probabilities of the oscillation conditions (packet L4a2)

Source: [2] (5.16), Lemmas 5.5, 5.7, 5.9 (TeX l. 2158–2389); planning audit MA7 D-OSC
("*Probabilities.*"); blueprint Lemma `r2:lem:oscconds`(a)–(c).

Every condition is a family of sub-scale oscillation bounds for one band version, so L3b2's
`prob_multiscaleOsc_compl_le` (`P[∃ k, osc_{B̄_{r_k a}(y_k)} X > r_k T] ≤ #family · 2e^{-(T-C)²/C}`,
`a` the smallest scale of the band) applies:

* `prob_not_niceOscCond_le_card` ((a′) for `B_{s_j}(s_j u)`): the band `h_{n-a_j,n-a_{j-1}}` has
  smallest scale `a = s_{j-1}`; the boxes are `B̄_{8s_i}(s_i v)` with `r = 8 s_i/s_{j-1}`, the slope
  is `T = K√a_{j-1}/8` (so `r T = K√a_{j-1} 2^{-(a_{j-1}-a_i)}`), and the family (`i < j`,
  `s_i v ∈ B_{4s_j}(s_j u)`) has at most `j (9·2^{a_j})^d` members;
  `prob_not_niceOscCond_le`: for DGZ's sequence and `K ≥ K₀`, `P[(a′) fails] ≤ e^{-K a_j}`
  (blueprint `r2:lem:oscconds`(a), with constant `1`);
* `prob_not_niceOscOne_le` ((1′) for `B_{s₁}(s₁ u)`): band `h_{n-a₁,n}`, `a = s₀`, `r = 3`,
  `T = L/3`, at most `(2·2^{a₁})^d` boxes (`r2:lem:oscconds`(b));
* `prob_not_eventJ2'_le_card` (`𝒥₂′`): band `h_{n-a_m}`, `a = s_m`, `r = 8 s_i/s_m`,
  `T = K√a_m/8`, at most `(m+1)(7·2^n)^d` boxes (`r2:lem:oscconds`(c); the final exponential bound
  is in `BadBoxJ.lean`).
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

/-! ## Condition (a′) -/

/-- **(a′) fails with probability at most `#family · 2e^{-(T-C)²/C}`** (MA7 D-OSC; blueprint
`r2:lem:oscconds`(a)): for a dyadic realization, a monotone exponent sequence, `1 ≤ j`, `a_j ≤ n`
and the slope `T = K√a_{j-1}/8 ≥ C`, the `a_j`-box `B_{s_j}(s_j u)` fails (a′) with probability at
most `j (9·2^{a_j})^d · 2e^{-(T-C)²/C}`. -/
theorem prob_not_niceOscCond_le_card {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, Monotone p.a → ∀ j : ℕ, 1 ≤ j → p.a j ≤ p.n →
          C ≤ p.K * √(p.a (j - 1) : ℝ) / 8 → ∀ u : Zd d,
            P {ω | ¬ NiceOscCond p (fun q z => H q z ω) j u} ≤
              ENNReal.ofReal (j * ((9 : ℝ) * 2 ^ p.a j) ^ d *
                (2 * Real.exp (-(p.K * √(p.a (j - 1) : ℝ) / 8 - C) ^ 2 / C))) := by
  obtain ⟨C, hC, hosc⟩ := prob_multiscaleOsc_compl_le.{0, 0} hκ
  refine ⟨C, hC, fun Ω _ P W H hH p hmono j hj hjn hT u => ?_⟩
  classical
  have hj1 : p.a (j - 1) ≤ p.a j := hmono (Nat.sub_le j 1)
  have hj1n : p.a (j - 1) ≤ p.n := hj1.trans hjn
  have hX := isBandVersion_sub_of_realization hκ hH (Nat.sub_le_sub_left hj1 p.n)
  have hs' := p.s_pos (j - 1)
  -- the family of boxes
  set N : ℕ → ℕ := fun i => 2 ^ ((p.n - p.a i) - (p.n - p.a j)) with hN
  set F : Finset (ℕ × Zd d) := (Finset.range j).biUnion fun i =>
    (BadBox.cube ((N i : ℤ) • u) (4 * N i)).image fun v => (i, v) with hF
  have hbound := hosc (P := P) hH.whiteNoise (a := p.s (j - 1)) hs' hX F
    (fun k => latPt (p.s k.1) k.2) (fun k => 8 * (p.s k.1 / p.s (j - 1)))
    (fun k _ => by have := p.s_pos k.1; positivity) hT
  refine (measure_mono ?_).trans (hbound.trans ?_)
  · intro ω hω
    simp only [mem_ofPred_eq, NiceOscCond] at hω
    push Not at hω
    obtain ⟨i, hi, v, hv, z, hz, w, hw, hlt⟩ := hω
    have hij : p.a i ≤ p.a (j - 1) := hmono (by omega)
    have hsi : p.s j = (N i : ℝ) * p.s i := by
      have := BadBox.s_eq_pow_mul p (i := i) (j := j) (Nat.sub_le_sub_left (hmono (by omega)) _)
      rw [this]
    have hr : 8 * (p.s i / p.s (j - 1)) * p.s (j - 1) = 8 * p.s i := by
      field_simp
    refine ⟨(i, v), ?_, z, ?_, w, ?_, ?_⟩
    · simp only [hF, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
      refine ⟨i, hi, v, ?_, rfl⟩
      refine BadBox.mem_cube_of_latPt_mem_obox (p.s_pos i) (N i) 4 u v ?_
      rw [← hsi]
      exact hv
    · show z ∈ cbox (latPt (p.s i) v) (8 * (p.s i / p.s (j - 1)) * p.s (j - 1))
      rw [hr]
      exact hz
    · show w ∈ cbox (latPt (p.s i) v) (8 * (p.s i / p.s (j - 1)) * p.s (j - 1))
      rw [hr]
      exact hw
    · show 8 * (p.s i / p.s (j - 1)) * (p.K * √(p.a (j - 1) : ℝ) / 8) <
        |(H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω) -
          (H (p.n - p.a (j - 1)) w ω - H (p.n - p.a j) w ω)|
      rw [BadBox.s_div_s_eq p hij hj1n]
      calc 8 * (2 : ℝ)⁻¹ ^ (p.a (j - 1) - p.a i) * (p.K * √(p.a (j - 1) : ℝ) / 8)
          = p.K * √(p.a (j - 1) : ℝ) * (2 : ℝ)⁻¹ ^ (p.a (j - 1) - p.a i) := by ring
        _ < _ := hlt
  · -- the number of boxes
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hcard : F.card ≤ j * (8 * 2 ^ p.a j + 1) ^ d := by
      refine (Finset.card_biUnion_le).trans ?_
      calc ∑ i ∈ Finset.range j,
            ((BadBox.cube ((N i : ℤ) • u) (4 * N i)).image fun v => (i, v)).card
          ≤ ∑ _i ∈ Finset.range j, (8 * 2 ^ p.a j + 1) ^ d := by
            refine Finset.sum_le_sum fun i _ => (Finset.card_image_le).trans ?_
            rw [BadBox.card_cube]
            have hNi : N i ≤ 2 ^ p.a j := by
              simp only [hN]
              exact Nat.pow_le_pow_right two_pos (by omega)
            have : 2 * (4 * N i) + 1 ≤ 8 * 2 ^ p.a j + 1 := by omega
            exact Nat.pow_le_pow_left this d
        _ = j * (8 * 2 ^ p.a j + 1) ^ d := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h1 : ((8 * 2 ^ p.a j + 1 : ℕ) : ℝ) ≤ (9 : ℝ) * 2 ^ p.a j := by
      push_cast
      have : (1 : ℝ) ≤ 2 ^ p.a j := one_le_pow₀ (by norm_num)
      linarith
    calc (F.card : ℝ) ≤ ((j * (8 * 2 ^ p.a j + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = (j : ℝ) * ((8 * 2 ^ p.a j + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
      _ ≤ (j : ℝ) * ((9 : ℝ) * 2 ^ p.a j) ^ d := by gcongr

/-- **(a′) fails with probability at most `e^{-K a_j}`** (MA7 D-OSC, [2] (5.16); blueprint
`r2:lem:oscconds`(a)): for DGZ's sequence (`0 ≤ λ ≤ 1/4`) there is `K₀` such that for `K ≥ K₀`,
every dyadic realization, `2 ≤ j`, `a_j ≤ n` and every `u`,
`P[B_{s_j}(s_j u) fails (a′)] ≤ e^{-K a_j}`. -/
theorem prob_not_niceOscCond_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ 1 / 4) :
    ∃ K₀ : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, K₀ ≤ p.K → p.a = dgzSeq lam p.K → ∀ j : ℕ, 2 ≤ j → p.a j ≤ p.n →
          ∀ u : Zd d, P {ω | ¬ NiceOscCond p (fun q z => H q z ω) j u} ≤
            ENNReal.ofReal (Real.exp (-(p.K * p.a j : ℝ))) := by
  obtain ⟨C, hC, hcard⟩ := prob_not_niceOscCond_le_card (d := d) hκ
  refine ⟨⌈512 * C + 256 * C * (3 + 5 * d) + 16 * C + 1⌉₊ + 2,
    fun Ω _ P W H hH p hK ha j hj hjn u => ?_⟩
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hK' : 512 * C + 256 * C * (3 + 5 * d) + 16 * C + 1 ≤ (p.K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_add_right _ 2).trans hK)
  have hK2 : 2 ≤ p.K := (Nat.le_add_left 2 _).trans hK
  have hK1 : 1 ≤ p.K := by omega
  have hmono : Monotone p.a := by rw [ha]; exact dgzSeq_monotone hlam0 hK1
  -- `N = a_{j-1} ≥ K⁴`, `a_j ≤ 2 a_{j-1}`, `j ≤ a_j`
  have hN : (p.K : ℝ) ^ 4 ≤ p.a (j - 1) := by
    have : p.K ^ 4 ≤ p.a (j - 1) := by rw [ha]; exact pow_le_dgzSeq hlam0 hK1 (by omega)
    exact_mod_cast this
  have hK16 : (16 : ℝ) ≤ (p.K : ℝ) ^ 4 := by
    have : (2 : ℝ) ≤ p.K := by exact_mod_cast hK2
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ (p.K : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
  have hM : (p.a j : ℝ) ≤ 2 * p.a (j - 1) := by
    have h1 : (p.a (j - 1 + 1) : ℝ) ≤ (1 + lam) * p.a (j - 1) + 1 := by
      rw [ha]
      exact dgzSeq_succ_le hlam0 (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at h1
    nlinarith
  have hJ : j ≤ p.a j := by rw [ha]; exact le_dgzSeq hlam0 hK1 j
  -- the slope is at least `C`
  have hT : C ≤ p.K * √(p.a (j - 1) : ℝ) / 8 := by
    have hsq : (p.K : ℝ) ^ 2 ≤ √(p.a (j - 1) : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      calc ((p.K : ℝ) ^ 2) ^ 2 = (p.K : ℝ) ^ 4 := by ring
        _ ≤ _ := hN
    have hK1' : (1 : ℝ) ≤ p.K := by exact_mod_cast hK1
    have h1 : (p.K : ℝ) ≤ p.K * √(p.a (j - 1) : ℝ) := by
      calc (p.K : ℝ) = p.K * 1 := (mul_one _).symm
        _ ≤ p.K * √(p.a (j - 1) : ℝ) :=
            mul_le_mul_of_nonneg_left ((one_le_pow₀ hK1').trans hsq) (by positivity)
    have : 0 ≤ 256 * C * (3 + 5 * (d : ℝ)) := by positivity
    linarith
  refine (hcard Ω P W H hH p hmono j (by omega) hjn hT u).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact BadBox.osc_arith hC d hK' hN hM hJ

/-! ## Condition (1′) -/

/-- **(1′) fails with probability at most `(2·2^{a₁})^d · 2e^{-(L/3-C)²/C}`** (MA7 D-OSC; blueprint
`r2:lem:oscconds`(b)): for a dyadic realization, `a₀ = 0` and `L/3 ≥ C`. -/
theorem prob_not_niceOscOne_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.a 0 = 0 → C ≤ p.L / 3 → ∀ u : Zd d,
          P {ω | ¬ NiceOscOne p (fun q z => H q z ω) u} ≤
            ENNReal.ofReal (((2 : ℝ) * 2 ^ p.a 1) ^ d *
              (2 * Real.exp (-(p.L / 3 - C) ^ 2 / C))) := by
  obtain ⟨C, hC, hosc⟩ := prob_multiscaleOsc_compl_le.{0, 0} hκ
  refine ⟨C, hC, fun Ω _ P W H hH p ha0 hT u => ?_⟩
  have hX := isBandVersion_sub_of_realization hκ hH (Nat.sub_le p.n (p.a 1))
  have hs0 : (2 : ℝ)⁻¹ ^ p.n = p.s 0 := by simp only [NiceParams.s, ha0, Nat.sub_zero]
  have hX' := hX.congr_band hs0 rfl
  set N : ℕ := 2 ^ ((p.n - p.a 0) - (p.n - p.a 1)) with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hsN : p.s 1 = (N : ℝ) * p.s 0 :=
    BadBox.s_eq_pow_mul p (Nat.sub_le_sub_left (by rw [ha0]; exact Nat.zero_le _) _)
  have hbound := hosc (P := P) hH.whiteNoise (a := p.s 0) (p.s_pos 0) hX'
    (BadBox.cube ((N : ℤ) • u) (N - 1)) (fun v => latPt (p.s 0) v) (fun _ => 3)
    (fun _ _ => by norm_num) hT
  refine (measure_mono ?_).trans (hbound.trans ?_)
  · intro ω hω
    simp only [mem_ofPred_eq, NiceOscOne] at hω
    push Not at hω
    obtain ⟨v, hv, z, hz, w, hw, hlt⟩ := hω
    refine ⟨v, ?_, z, hz, w, hw, ?_⟩
    · rw [hsN] at hv
      exact (BadBox.latPt_mem_obox_iff_mem_cube (p.s_pos 0) N hN1 u v).1 hv
    · show 3 * (p.L / 3) < |(H p.n z ω - H (p.n - p.a 1) z ω) -
        (H p.n w ω - H (p.n - p.a 1) w ω)|
      rw [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
      exact hlt
  · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [BadBox.card_cube]
    have hNle : N ≤ 2 ^ p.a 1 := Nat.pow_le_pow_right two_pos (by omega)
    have h1 : 2 * (N - 1) + 1 ≤ 2 * 2 ^ p.a 1 := by omega
    calc (((2 * (N - 1) + 1) ^ d : ℕ) : ℝ) ≤ (((2 * 2 ^ p.a 1) ^ d : ℕ) : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_left h1 d
      _ = ((2 : ℝ) * 2 ^ p.a 1) ^ d := by push_cast; ring

/-! ## The event `𝒥₂′` -/

/-- **`𝒥₂′` fails with probability at most `(m+1)(7·2^n)^d · 2e^{-(T-C)²/C}`** (MA7 D-OSC;
blueprint `r2:lem:oscconds`(c)): for a dyadic realization, a monotone exponent sequence, `a_m ≤ n`
and the slope `T = K√a_m/8 ≥ C`. -/
theorem prob_not_eventJ2'_le_card {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, Monotone p.a → ∀ m : ℕ, p.a m ≤ p.n →
          C ≤ p.K * √(p.a m : ℝ) / 8 →
            P {ω | ¬ EventJ2' p (fun q z => H q z ω) m} ≤
              ENNReal.ofReal ((m + 1) * ((7 : ℝ) * 2 ^ p.n) ^ d *
                (2 * Real.exp (-(p.K * √(p.a m : ℝ) / 8 - C) ^ 2 / C))) := by
  obtain ⟨C, hC, hosc⟩ := prob_multiscaleOsc_compl_le.{0, 0} hκ
  refine ⟨C, hC, fun Ω _ P W H hH p hmono m hmn hT => ?_⟩
  classical
  have hX := hH.band (p.n - p.a m)
  have hsm := p.s_pos m
  set F : Finset (ℕ × Zd d) := (Finset.range (m + 1)).biUnion fun i =>
    (BadBox.cube 0 (3 * 2 ^ (p.n - p.a i))).image fun v => (i, v) with hF
  have hbound := hosc (P := P) hH.whiteNoise (a := p.s m) hsm hX F
    (fun k => latPt (p.s k.1) k.2) (fun k => 8 * (p.s k.1 / p.s m))
    (fun k _ => by have := p.s_pos k.1; positivity) hT
  refine (measure_mono ?_).trans (hbound.trans ?_)
  · intro ω hω
    simp only [mem_ofPred_eq, EventJ2'] at hω
    push Not at hω
    obtain ⟨i, hi, v, hv, z, hz, w, hw, hlt⟩ := hω
    have hr : 8 * (p.s i / p.s m) * p.s m = 8 * p.s i := by field_simp
    refine ⟨(i, v), ?_, z, ?_, w, ?_, ?_⟩
    · simp only [hF, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
      refine ⟨i, Nat.lt_succ_of_le hi, v, ?_, rfl⟩
      refine BadBox.mem_cube_zero_of_latPt_mem_obox (p.s_pos i) _ ?_ v hv
      have e : ((3 * 2 ^ (p.n - p.a i) : ℕ) : ℝ) * p.s i = 3 := by
        unfold NiceParams.s
        push_cast
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, mul_one]
      rw [e]
    · show z ∈ cbox (latPt (p.s i) v) (8 * (p.s i / p.s m) * p.s m)
      rw [hr]
      exact hz
    · show w ∈ cbox (latPt (p.s i) v) (8 * (p.s i / p.s m) * p.s m)
      rw [hr]
      exact hw
    · show 8 * (p.s i / p.s m) * (p.K * √(p.a m : ℝ) / 8) <
        |H (p.n - p.a m) z ω - H (p.n - p.a m) w ω|
      rw [BadBox.s_div_s_eq p (hmono hi) hmn]
      calc 8 * (2 : ℝ)⁻¹ ^ (p.a m - p.a i) * (p.K * √(p.a m : ℝ) / 8)
          = p.K * √(p.a m : ℝ) * (2 : ℝ)⁻¹ ^ (p.a m - p.a i) := by ring
        _ < _ := hlt
  · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hcard : F.card ≤ (m + 1) * (6 * 2 ^ p.n + 1) ^ d := by
      refine (Finset.card_biUnion_le).trans ?_
      calc ∑ i ∈ Finset.range (m + 1),
            ((BadBox.cube 0 (3 * 2 ^ (p.n - p.a i))).image fun v => (i, v)).card
          ≤ ∑ _i ∈ Finset.range (m + 1), (6 * 2 ^ p.n + 1) ^ d := by
            refine Finset.sum_le_sum fun i _ => (Finset.card_image_le).trans ?_
            rw [BadBox.card_cube]
            have h2 : 2 ^ (p.n - p.a i) ≤ 2 ^ p.n := Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)
            have : 2 * (3 * 2 ^ (p.n - p.a i)) + 1 ≤ 6 * 2 ^ p.n + 1 := by omega
            exact Nat.pow_le_pow_left this d
        _ = (m + 1) * (6 * 2 ^ p.n + 1) ^ d := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h1 : ((6 * 2 ^ p.n + 1 : ℕ) : ℝ) ≤ (7 : ℝ) * 2 ^ p.n := by
      push_cast
      have : (1 : ℝ) ≤ 2 ^ p.n := one_le_pow₀ (by norm_num)
      linarith
    calc (F.card : ℝ) ≤ (((m + 1) * (6 * 2 ^ p.n + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = ((m : ℝ) + 1) * ((6 * 2 ^ p.n + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
      _ ≤ ((m : ℝ) + 1) * ((7 : ℝ) * 2 ^ p.n) ^ d := by gcongr

end DGZ

end HigherDimLQGMetric
