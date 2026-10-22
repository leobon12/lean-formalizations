import HigherDimLQGMetric.DGZ.CompareProp51

/-!
# DGZ Corollary 5.2, right inequality (packet L4c)

Source: [2] Cor 5.2 (TeX l. 2009–2027), the direction used (MA7 D-5.2; blueprint Part C
`r2:cor:52`; ruling M23 (iii)): the interface shape `Cor52Shape` of the orchestrator-owned module
`DGZ/Interfaces.lean` (verbatim MA7 Details (c)).

**Statement** (`cor52Shape : ∀ d κ ξ Q, Cor52Shape d κ ξ Q`). Under `DGZHyp`, for `ε > 0` and
`0 < q < q' < 1` there is `C` such that for every dyadic realization and all `0 ≤ k ≤ n`:
`a^{(q)}_{n-k} ≤ C 2^{(1-ξQ+ε)k} a^{(q')}_n`.

**Proof** (three-case split of ruling M23 (iii), blueprint `r2:cor:52`). Let `c, N` be the
constants of the restricted Proposition 5.1 (`prop51Shape`), `N₁ ≥ N` with `2^{-cN₁} ≤ q' - q`,
and `η := εc/(2(1+c))`.
* `k = 0`: `a^{(q)}_n ≤ a^{(q')}_n` (monotonicity of the lower quantile) and `C ≥ 1`.
* `k ≥ 1`, `k ≤ c(n-k)`, `n - k ≥ N₁`: Proposition 5.1 at `(n-k, k)` gives
  `P[D_n ≤ c 2^{-(1-ξQ+ε)k} D_{n-k}] ≤ q' - q`; on `{D_n ≤ a^{(q')}_n}` minus this event,
  `D_{n-k} < c⁻¹ 2^{(1-ξQ+ε)k} a^{(q')}_n`; so this value has probability `≥ q` under the law of
  `D_{n-k}`, and `a^{(q)}_{n-k} ≤ c⁻¹ 2^{(1-ξQ+ε)k} a^{(q')}_n`
  (`le_measure_Iic_iff_lowerQuantile_le`).
* otherwise (`k > c(n-k)` or `n - k < N₁`): L3c2's quantile bounds (`exists_aQ_le`,
  `exists_le_aQ`, uniform in the realization) give `a^{(q)}_{n-k} ≤ A 2^{-(1-ξQ-η)(n-k)}` and
  `a^{(q')}_n ≥ c' 2^{-(1-ξQ+η)n}`; the ratio is `≤ (A/c') 2^E` with `E = 2ηn - (ε+η)k`, and
  `E < 0` if `k > c(n-k)` (as `2η(1+c) = εc`), `E ≤ 2ηN₁` if `n - k < N₁` (as `η ≤ ε`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-! ## Quantiles of `D_n(0, e₁; B₂(0))` -/

/-- The defining property of `a_N^{(p)}`: `p ≤ P[D_N ≤ x] ↔ a_N^{(p)} ≤ x` (`0 < p < 1`). -/
theorem cmp_le_prob_iff_aQ_le {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H) (ξ : ℝ)
    (N : ℕ) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) :
    p ≤ P {ω | lfppDistance d ξ (fun z => H N z ω) ≤ x} ↔ aQ P H ξ N p ≤ x := by
  have hPprob := hH.whiteNoise.isProbabilityMeasure
  have hm : Measurable fun ω => lfppDistance d ξ (fun z => H N z ω) :=
    (hH.band N).measurable_lfppDistance ξ
  unfold aQ
  rw [← LQGMetric.le_measure_Iic_iff_lowerQuantile_le hp0 hp1,
    Measure.map_apply hm measurableSet_Iic]
  rfl

/-- Monotonicity of `a_N^{(p)}` in `p`. -/
theorem cmp_aQ_mono {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H) (ξ : ℝ)
    (N : ℕ) {q q' : ℝ≥0∞} (hq0 : 0 < q) (hqq' : q ≤ q') (hq'1 : q' < 1) :
    aQ P H ξ N q ≤ aQ P H ξ N q' := by
  have h1 := (cmp_le_prob_iff_aQ_le hH ξ N (hq0.trans_le hqq') hq'1 (aQ P H ξ N q')).2 le_rfl
  exact (cmp_le_prob_iff_aQ_le hH ξ N hq0 (hqq'.trans_lt hq'1) _).1 (hqq'.trans h1)

/-- `2^{-cn} ≤ g` for large `n` (`c, g > 0`). -/
theorem cmp_exists_two_rpow_le {c g : ℝ} (hc : 0 < c) (hg : 0 < g) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (2 : ℝ) ^ (-(c * n)) ≤ g := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨⌈1 / (c * g * Real.log 2)⌉₊, fun n hn => ?_⟩
  have hn' : 1 / (c * g * Real.log 2) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [Real.rpow_neg two_pos.le, inv_le_comm₀ (Real.rpow_pos_of_pos two_pos _) hg,
    Real.rpow_def_of_pos two_pos]
  have h1 := Real.add_one_le_exp (Real.log 2 * (c * n))
  have h2 : g⁻¹ ≤ Real.log 2 * (c * n) := by
    rw [div_le_iff₀ (by positivity)] at hn'
    rw [inv_le_iff_one_le_mul₀ hg]
    nlinarith
  linarith

/-! ## Corollary 5.2 -/

/-- **DGZ Corollary 5.2, the direction used** (MA7 D-5.2; blueprint `r2:cor:52`; ruling M23
(iii)): the interface shape `Cor52Shape` holds for all `d κ ξ Q`. -/
theorem cor52Shape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Cor52Shape d κ ξ Q := by
  intro h ε hε q q' hq0 hqq' hq'1
  have hq1 : q < 1 := hqq'.trans hq'1
  have hq'0 : 0 < q' := hq0.trans hqq'
  obtain ⟨c, hc, N, hP51⟩ := prop51Shape d κ ξ Q h ε hε
  have hq'top : q' ≠ ⊤ := ne_top_of_lt hq'1
  have hgap : 0 < (q' - q).toReal :=
    ENNReal.toReal_pos (tsub_pos_of_lt hqq').ne' (ne_top_of_le_ne_top hq'top tsub_le_self)
  obtain ⟨N₁', hN₁'⟩ := cmp_exists_two_rpow_le hc hgap
  set N₁ : ℕ := max N N₁' with hN₁def
  set η : ℝ := ε * c / (2 * (1 + c)) with hηdef
  have hη : 0 < η := by positivity
  have hηc : 2 * η * (1 + c) = ε * c := by
    rw [hηdef]
    field_simp
  have hηε : η ≤ ε := by
    rw [hηdef, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨A, hA, haQ⟩ := exists_aQ_le h hq0 hq1 hη
  obtain ⟨c', hc', hlaQ⟩ := exists_le_aQ h hq'0 hq'1 hη
  set C₂ : ℝ := A / c' * (2 : ℝ) ^ (2 * η * N₁) with hC₂def
  have hC₂ : 0 < C₂ := by positivity
  refine ⟨max c⁻¹ (max C₂ 1), lt_of_lt_of_le (inv_pos.2 hc) (le_max_left _ _),
    fun Ω _ P W H hH n k hkn => ?_⟩
  set C : ℝ := max c⁻¹ (max C₂ 1) with hCdef
  have hpos : 0 < aQ P H ξ n q' :=
    lt_of_lt_of_le (by positivity) (hlaQ Ω P W H hH n)
  have hX : 0 < (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) := Real.rpow_pos_of_pos two_pos _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`
    have hC1 : 1 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
    simp only [Nat.sub_zero, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    calc aQ P H ξ n q ≤ aQ P H ξ n q' := cmp_aQ_mono hH ξ n hq0 hqq'.le hq'1
      _ ≤ C * aQ P H ξ n q' := le_mul_of_one_le_left hpos.le hC1
  by_cases hcase : (k : ℝ) ≤ c * ((n - k : ℕ) : ℝ) ∧ N₁ ≤ n - k
  · -- Proposition 5.1 at `(n - k, k)`
    obtain ⟨hkc, hN₁⟩ := hcase
    have hP := hP51 Ω P W H hH (n - k) k ((le_max_left _ _).trans hN₁) hk hkc
    rw [Nat.sub_add_cancel hkn] at hP
    have hsmall : ENNReal.ofReal ((2 : ℝ) ^ (-(c * ((n - k : ℕ) : ℝ)))) ≤ q' - q := by
      rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top hq'top tsub_le_self)]
      exact ENNReal.ofReal_le_ofReal (hN₁' _ ((le_max_right _ _).trans hN₁))
    set a : ℝ := aQ P H ξ n q' with hadef
    set X : ℝ := c⁻¹ * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * a with hXdef
    have hqa : q' ≤ P {ω | lfppDistance d ξ (fun z => H n z ω) ≤ a} :=
      (cmp_le_prob_iff_aQ_le hH ξ n hq'0 hq'1 a).2 le_rfl
    have hinc : {ω | lfppDistance d ξ (fun z => H n z ω) ≤ a} ⊆
        {ω | lfppDistance d ξ (fun z => H (n - k) z ω) ≤ X} ∪
        {ω | lfppDistance d ξ (fun z => H n z ω) ≤
          c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * lfppDistance d ξ (fun z => H (n - k) z ω)} := by
      intro ω hω
      by_contra hcon
      simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hcon hω
      obtain ⟨h1, h2⟩ := hcon
      have hY : 0 < c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) :=
        mul_pos hc (Real.rpow_pos_of_pos two_pos _)
      have hYX : c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * X = a := by
        rw [hXdef]
        have e : (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) = 1 := by
          rw [← Real.rpow_add two_pos,
            show -(1 - ξ * Q + ε) * (k : ℝ) + (1 - ξ * Q + ε) * k = 0 by ring, Real.rpow_zero]
        calc c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * (c⁻¹ * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * a)
            = (c * c⁻¹) * ((2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k)) *
                a := by ring
          _ = a := by rw [mul_inv_cancel₀ hc.ne', e, one_mul, one_mul]
      have := mul_lt_mul_of_pos_left h1 hY
      linarith
    have hsum : q' ≤ P {ω | lfppDistance d ξ (fun z => H (n - k) z ω) ≤ X} + (q' - q) :=
      hqa.trans ((measure_mono hinc).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl (hP.trans hsmall))))
    have hq : q ≤ P {ω | lfppDistance d ξ (fun z => H (n - k) z ω) ≤ X} := by
      have := tsub_le_iff_right.2 hsum
      rwa [ENNReal.sub_sub_cancel hq'top hqq'.le] at this
    have hle := (cmp_le_prob_iff_aQ_le hH ξ (n - k) hq0 hq1 X).1 hq
    calc aQ P H ξ (n - k) q ≤ X := hle
      _ = c⁻¹ * ((2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * a) := by rw [hXdef, mul_assoc]
      _ ≤ C * ((2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * a) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = C * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * a := by ring
  · -- the quantile asymptotics
    have h1 := haQ Ω P W H hH (n - k)
    have h2 := hlaQ Ω P W H hH n
    have hnk : ((n - k : ℕ) : ℝ) = n - k := Nat.cast_sub hkn
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    set E : ℝ := 2 * η * n - (ε + η) * k with hEdef
    have hE : E ≤ 2 * η * N₁ := by
      rw [not_and_or, not_le, not_le] at hcase
      rcases hcase with hlt | hlt
      · -- `k > c (n - k)`: `E < 0`
        rw [hnk] at hlt
        have hN₁0 : (0 : ℝ) ≤ 2 * η * N₁ := by positivity
        have e1 : 2 * η * (1 + c) * k = ε * c * k := by rw [hηc]
        have e2 : 2 * η * (c * (n - k)) < 2 * η * k := mul_lt_mul_of_pos_left hlt (by positivity)
        have e3 : 0 ≤ η * c * k := by positivity
        have hcE : c * E ≤ c * 0 := by
          rw [hEdef]
          linarith
        have : E ≤ 0 := le_of_mul_le_mul_left hcE hc
        linarith
      · -- `n - k < N₁`
        have hlt' : ((n - k : ℕ) : ℝ) < N₁ := by exact_mod_cast hlt
        rw [hnk] at hlt'
        rw [hEdef]
        nlinarith
    have hsplit : (2 : ℝ) ^ (-(1 - ξ * Q - η) * ((n - k : ℕ) : ℝ)) =
        (2 : ℝ) ^ E * ((2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)) := by
      rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos, hnk, hEdef]
      ring_nf
    have hEle : (2 : ℝ) ^ E ≤ (2 : ℝ) ^ (2 * η * N₁) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two hE
    calc aQ P H ξ (n - k) q ≤ A * (2 : ℝ) ^ (-(1 - ξ * Q - η) * ((n - k : ℕ) : ℝ)) := h1
      _ = A / c' * (2 : ℝ) ^ E * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) *
            (c' * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)) := by
          rw [hsplit]
          field_simp
      _ ≤ A / c' * (2 : ℝ) ^ (2 * η * N₁) * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) *
            aQ P H ξ n q' := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEle
            (by positivity)) hX.le) h2 (by positivity) (by positivity)
      _ ≤ C * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * aQ P H ξ n q' := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hX.le) hpos.le
          exact (le_max_left _ _).trans (le_max_right _ _)

end DGZ

end HigherDimLQGMetric
