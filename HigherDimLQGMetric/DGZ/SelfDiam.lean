import HigherDimLQGMetric.DGZ.Chain
import HigherDimLQGMetric.DGZ.Sec41Prob
import HigherDimLQGMetric.DGZ.ConcentrationFunctionals
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# DGZ Prop 4.7, upper half, self-internal form (packet L3c2; MA7 D-4.7s)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Prop 4.7 (TeX l. 1621–1667, p. 32); planning
audit `planning/audits/MA7-ref2-sections-4-6.md`, §5 row L3c2, gaps G6/G7 and Details (a) D-4.7s
(avoids Lemma 4.2(2)); the target shape `SelfDiamShape` is copied **verbatim** from MA7 Details (c)
§E (durable copy `planning/audits/statements/MA7Statements.lean.txt`).

Main results:
* `SelfDiamShape` (definition, verbatim) and `selfDiamShape : SelfDiamShape d κ ξ Q` (for all
  `d, κ, ξ, Q`): under `DGZHyp d κ ξ Q`, for every `δ > 0` there is `C` with
  `P*[selfDiam_n(B₁(0)) > 2^{-(1-ξQ-δ)n}] ≤ C e^{-n/C}` for every dyadic realization and every `n`;
* `selfDiam_tail`: the same for `B_ρ(0)`, with one `C` for all `ρ ∈ [1, 3/2]`;
* `aQ_eq_of_isDyadicRealization`: the quantiles `a^{(p)}_N` do not depend on the realization;
* `exists_aQ_le`: `a^{(q)}_N ≤ A 2^{-(1-ξQ-ε)N}` for all `N`, uniformly in the realization
  (`IsDGZExponent` on one reference realization and DGZ Lemma 3.2);
* `prob_eventA_compl_le`: `P[𝒜_{r,n}ᶜ] ≤ C e^{-r/C}` for `1 ≤ r < n` (Lemma 4.2(1) and a union
  bound), with one `c₄ < 1` and one `C`.

Proof of `selfDiam_tail` (MA7 D-4.7s): `η := min(δ, ξ(Q-√(2d)))/2`, `q ∈ (c₄(η), 1)`; `r ≥ 110`
with `P[𝒜_{r,n}ᶜ] ≤ 1/4` for all `n > r`. On `𝒜_{r,n}`, `chain_selfInternal` (ii) and
`a^{(q)}_N ≤ A 2^{-(1-ξQ-η/2)N}` give `selfDiam_n(B_ρ(0)) ≤ K 2^{-(1-ξQ-η/2)n}` with
`K = C_d 2^r (A S + S) + 1`, `S = Σ_k k^{2d} 2^{-3ηk/2}`; so the lower `3/4`-quantile is below this
level, and D-4.6 (L3b2's `integral_log_lt_log_add_of_le_measure_le` and
`measure_lt_le_of_integral_log_add_le`, variance `n log 2`) gives the tail
`2 exp(-(δ log 2)² n/(32 ξ² log 2))` for `n ≥ n₁`; small `n` are absorbed in `C`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)
open HigherDimLFPP.Conc (quantileConst)

variable {d : ℕ}

/-! ### The target shape (MA7 Details (c) §E, verbatim) -/

/-- **DGZ Prop 4.7, self-internal form, upper half** (MA7 D-4.7s): the self-internal diameter of
`B₁(0)` is `≤ 2^{-(1-ξQ-δ)n}` outside an exponentially small event -/
def SelfDiamShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ δ > 0, ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
      P {ω | (2 : ℝ) ^ (-(1 - ξ * Q - δ) * n) < selfDiam ξ (fun z => H n z ω) 0 1} ≤
        ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C))

/-! ### Quantiles -/

/-- **Law transfer**: the lower quantiles `a^{(p)}_N` of `D_N(0, e₁; B₂(0))` are the same for every
dyadic realization (the laws of `D_N` agree, HigherDimLFPP `IsBandVersion.map_lfppDistance_eq`). -/
theorem aQ_eq_of_isDyadicRealization {κ : Rd d → ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} {W : WN d → Ω → ℝ}
    {W' : WN d → Ω' → ℝ} {H : ℕ → Rd d → Ω → ℝ} {H' : ℕ → Rd d → Ω' → ℝ}
    (hH : IsDyadicRealization κ P W H) (hH' : IsDyadicRealization κ P' W' H') (ξ : ℝ) (N : ℕ)
    (p : ℝ≥0∞) : aQ P H ξ N p = aQ P' H' ξ N p := by
  unfold aQ
  rw [(hH.band N).map_lfppDistance_eq (hH'.band N) hH.whiteNoise hH'.whiteNoise ξ
    (HigherDimLFPP.DGZ.measurable_lfppDistance_continuousMap ξ)]

/-- `exp(K √(N log 2)) ≤ exp(K²/(2ε)) 2^{εN/2}` for `ε > 0` (from `K u ≤ (ε/2) u² + K²/(2ε)`). -/
lemma exp_mul_sqrt_le (K : ℝ) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    Real.exp (K * √(N * Real.log 2)) ≤ Real.exp (K ^ 2 / (2 * ε)) * (2 : ℝ) ^ (ε / 2 * N) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, √(N * Real.log 2) = u := ⟨_, rfl⟩
  have hu2 : u ^ 2 = N * Real.log 2 := by rw [← hudef]; exact Real.sq_sqrt (by positivity)
  rw [hudef]
  have key : K * u ≤ K ^ 2 / (2 * ε) + ε / 2 * N * Real.log 2 := by
    have h0 : 0 ≤ ε / 2 * (u - K / ε) ^ 2 := by positivity
    have e : ε / 2 * (u - K / ε) ^ 2 = ε / 2 * u ^ 2 - K * u + K ^ 2 / (2 * ε) := by
      field_simp
      ring
    rw [hu2] at e
    nlinarith
  calc Real.exp (K * u) ≤ Real.exp (K ^ 2 / (2 * ε) + ε / 2 * N * Real.log 2) :=
        Real.exp_le_exp.2 key
    _ = Real.exp (K ^ 2 / (2 * ε)) * (2 : ℝ) ^ (ε / 2 * N) := by
      rw [Real.exp_add, Real.rpow_def_of_pos two_pos,
        show Real.log 2 * (ε / 2 * N) = ε / 2 * N * Real.log 2 by ring]

/-- **Uniform bound on the quantiles** (MA7 D-4.7s, "by `IsDGZExponent` and HA5-D3"): under
`DGZHyp d κ ξ Q`, for `q ∈ (0, 1)` and `ε > 0` there is `A > 0` with
`a^{(q)}_N ≤ A 2^{-(1-ξQ-ε)N}` for all `N` and every dyadic realization. -/
theorem exists_aQ_le {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {q : ℝ≥0∞} (hq0 : 0 < q)
    (hq1 : q < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ A > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ N : ℕ,
        aQ P H ξ N q ≤ A * (2 : ℝ) ^ (-(1 - ξ * Q - ε) * N) := by
  by_cases hex : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H
  swap
  · exact ⟨1, one_pos, fun Ω _ P W H hH => absurd ⟨Ω, _, P, W, H, hH⟩ hex⟩
  obtain ⟨Ω₀, m₀, P₀, W₀, H₀, h₀⟩ := hex
  suffices hsuff : ∃ A > 0, ∀ N : ℕ, aQ P₀ H₀ ξ N q ≤ A * (2 : ℝ) ^ (-(1 - ξ * Q - ε) * N) by
    obtain ⟨A, hA, hb⟩ := hsuff
    refine ⟨A, hA, fun Ω _ P W H hH N => ?_⟩
    rw [aQ_eq_of_isDyadicRealization hH h₀]
    exact hb N
  have hd0 : 0 < d := by have := h.dim; omega
  have hξ := h.xi_pos
  have hW₀ := h₀.whiteNoise
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- (a) the median: eventually `a^{(1/2)}_N ≤ 2^{-(1-ξQ-ε/2)N}` (`IsDGZExponent`)
  have hlim := h.exponent Ω₀ P₀ W₀ H₀ h₀
  have hlt : -(1 - ξ * Q) * Real.log 2 < -(1 - ξ * Q - ε / 2) * Real.log 2 := by nlinarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (Filter.Tendsto.eventually_lt_const hlt hlim)
  set N₁ : ℕ := max N₀ 1 with hN₁
  have hmed : ∀ N, N₁ ≤ N → aQ P₀ H₀ ξ N 2⁻¹ ≤ (2 : ℝ) ^ (-(1 - ξ * Q - ε / 2) * N) := by
    intro N hN
    have h1 := hN₀ N (le_trans (le_max_left _ _) hN)
    have hNpos : (0 : ℝ) < N := by
      have : 1 ≤ N := le_trans (le_max_right _ _) hN
      exact_mod_cast this
    rw [div_lt_iff₀ hNpos] at h1
    by_cases hpos : 0 < aQ P₀ H₀ ξ N 2⁻¹
    · calc aQ P₀ H₀ ξ N 2⁻¹ = Real.exp (Real.log (aQ P₀ H₀ ξ N 2⁻¹)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (-(1 - ξ * Q - ε / 2) * Real.log 2 * N) := Real.exp_le_exp.2 h1.le
        _ = (2 : ℝ) ^ (-(1 - ξ * Q - ε / 2) * N) := by
          rw [Real.rpow_def_of_pos two_pos]
          congr 1
          ring
    · exact (not_lt.1 hpos).trans (Real.rpow_nonneg (by norm_num) _)
  -- (b) DGZ Lemma 3.2: `a^{(q)}_N ≤ exp(K₁ √(N log 2)) a^{(1/2)}_N`
  set K₁ : ℝ := (quantileConst (2⁻¹ : ℝ≥0∞).toReal + quantileConst q.toReal) * ξ with hK₁
  have hcmp : ∀ N, 1 ≤ N →
      aQ P₀ H₀ ξ N q ≤ Real.exp (K₁ * √(N * Real.log 2)) * aQ P₀ H₀ ξ N 2⁻¹ := by
    intro N hN
    have hab : (2 : ℝ)⁻¹ ^ N < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have h1 := (h₀.band N).lowerQuantile_lfppDistance_le_exp_mul hd0 h.kernel hW₀
      (by positivity) hab hξ (p₁ := 2⁻¹) (p₂ := q) (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
      (ENNReal.inv_lt_one.2 (by norm_num)) hq0 hq1
    rw [log_one_div_inv_two_pow] at h1
    unfold aQ
    calc _ ≤ _ := h1
      _ = _ := by rw [hK₁]
  -- (d) large `N`
  have hbig : ∀ N, N₁ ≤ N →
      aQ P₀ H₀ ξ N q ≤ Real.exp (K₁ ^ 2 / (2 * ε)) * (2 : ℝ) ^ (-(1 - ξ * Q - ε) * N) := by
    intro N hN
    have h1 := hcmp N (le_trans (le_max_right _ _) hN)
    have h2 := hmed N hN
    have h3 := exp_mul_sqrt_le K₁ hε N
    have hexp0 := Real.exp_pos (K₁ * √(N * Real.log 2))
    calc aQ P₀ H₀ ξ N q ≤ Real.exp (K₁ * √(N * Real.log 2)) * aQ P₀ H₀ ξ N 2⁻¹ := h1
      _ ≤ Real.exp (K₁ * √(N * Real.log 2)) * (2 : ℝ) ^ (-(1 - ξ * Q - ε / 2) * N) :=
          mul_le_mul_of_nonneg_left h2 hexp0.le
      _ ≤ Real.exp (K₁ ^ 2 / (2 * ε)) * (2 : ℝ) ^ (ε / 2 * N) *
            (2 : ℝ) ^ (-(1 - ξ * Q - ε / 2) * N) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (by norm_num) _)
      _ = Real.exp (K₁ ^ 2 / (2 * ε)) * (2 : ℝ) ^ (-(1 - ξ * Q - ε) * N) := by
          rw [mul_assoc, ← Real.rpow_add two_pos]
          congr 2
          ring
  -- (e) small `N`
  set A : ℝ := Real.exp (K₁ ^ 2 / (2 * ε)) +
    ∑ m ∈ Finset.range N₁, |aQ P₀ H₀ ξ m q| * (2 : ℝ) ^ ((1 - ξ * Q - ε) * m) with hA
  have hsum0 : 0 ≤ ∑ m ∈ Finset.range N₁, |aQ P₀ H₀ ξ m q| * (2 : ℝ) ^ ((1 - ξ * Q - ε) * m) :=
    Finset.sum_nonneg fun m _ => by positivity
  refine ⟨A, by positivity, fun N => ?_⟩
  have hpow0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 - ξ * Q - ε) * N) := Real.rpow_nonneg (by norm_num) _
  rcases lt_or_ge N N₁ with hN | hN
  · have hterm : |aQ P₀ H₀ ξ N q| * (2 : ℝ) ^ ((1 - ξ * Q - ε) * N) ≤ A := by
      have := Finset.single_le_sum
        (f := fun m => |aQ P₀ H₀ ξ m q| * (2 : ℝ) ^ ((1 - ξ * Q - ε) * m))
        (fun m _ => by positivity) (Finset.mem_range.2 hN)
      have := Real.exp_pos (K₁ ^ 2 / (2 * ε))
      linarith
    calc aQ P₀ H₀ ξ N q ≤ |aQ P₀ H₀ ξ N q| := le_abs_self _
      _ = |aQ P₀ H₀ ξ N q| * (2 : ℝ) ^ ((1 - ξ * Q - ε) * N) *
            (2 : ℝ) ^ (-(1 - ξ * Q - ε) * N) := by
          rw [mul_assoc, ← Real.rpow_add two_pos, show (1 - ξ * Q - ε) * (N : ℝ) +
            -(1 - ξ * Q - ε) * N = 0 by ring, Real.rpow_zero, mul_one]
      _ ≤ A * (2 : ℝ) ^ (-(1 - ξ * Q - ε) * N) := mul_le_mul_of_nonneg_right hterm hpow0
  · refine (hbig N hN).trans (mul_le_mul_of_nonneg_right ?_ hpow0)
    linarith

/-- **Uniform lower bound on the quantiles** (MA7 D-5.2, D-6.1: "`a^{(q')}_n ≥ c 2^{-(1-ξQ+ε)n}`
(`IsDGZExponent`, HA5-D3)"): under `DGZHyp d κ ξ Q`, for `q ∈ (0, 1)` and `ε > 0` there is `c > 0`
with `c 2^{-(1-ξQ+ε)N} ≤ a^{(q)}_N` for all `N` and every dyadic realization. -/
theorem exists_le_aQ {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {q : ℝ≥0∞} (hq0 : 0 < q)
    (hq1 : q < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ N : ℕ,
        c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * N) ≤ aQ P H ξ N q := by
  by_cases hex : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H
  swap
  · exact ⟨1, one_pos, fun Ω _ P W H hH => absurd ⟨Ω, _, P, W, H, hH⟩ hex⟩
  obtain ⟨Ω₀, m₀, P₀, W₀, H₀, h₀⟩ := hex
  suffices hsuff : ∃ c > 0, ∀ N : ℕ, c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * N) ≤ aQ P₀ H₀ ξ N q by
    obtain ⟨c, hc, hb⟩ := hsuff
    refine ⟨c, hc, fun Ω _ P W H hH N => ?_⟩
    rw [aQ_eq_of_isDyadicRealization hH h₀]
    exact hb N
  have hd0 : 0 < d := by have := h.dim; omega
  have hξ := h.xi_pos
  have hW₀ := h₀.whiteNoise
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpos : ∀ N : ℕ, ∀ p : ℝ≥0∞, 0 < p → p < 1 → 0 < aQ P₀ H₀ ξ N p := by
    intro N p hp0 hp1
    unfold aQ
    rw [(h₀.band N).lowerQuantile_lfppDistance_eq_exp hd0 hW₀ ξ hp0 hp1]
    exact Real.exp_pos _
  have hhalf0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hhalf1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  -- (a) the median: eventually `2^{-(1-ξQ+ε/2)N} ≤ a^{(1/2)}_N` (`IsDGZExponent`)
  have hlim := h.exponent Ω₀ P₀ W₀ H₀ h₀
  have hlt : -(1 - ξ * Q + ε / 2) * Real.log 2 < -(1 - ξ * Q) * Real.log 2 := by nlinarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (Filter.Tendsto.eventually_const_lt hlt hlim)
  set N₁ : ℕ := max N₀ 1 with hN₁
  have hmed : ∀ N, N₁ ≤ N → (2 : ℝ) ^ (-(1 - ξ * Q + ε / 2) * N) ≤ aQ P₀ H₀ ξ N 2⁻¹ := by
    intro N hN
    have h1 := hN₀ N (le_trans (le_max_left _ _) hN)
    have hNpos : (0 : ℝ) < N := by
      have : 1 ≤ N := le_trans (le_max_right _ _) hN
      exact_mod_cast this
    rw [lt_div_iff₀ hNpos] at h1
    calc (2 : ℝ) ^ (-(1 - ξ * Q + ε / 2) * N)
        = Real.exp (-(1 - ξ * Q + ε / 2) * Real.log 2 * N) := by
          rw [Real.rpow_def_of_pos two_pos]
          congr 1
          ring
      _ ≤ Real.exp (Real.log (aQ P₀ H₀ ξ N 2⁻¹)) := Real.exp_le_exp.2 h1.le
      _ = aQ P₀ H₀ ξ N 2⁻¹ := Real.exp_log (hpos N 2⁻¹ hhalf0 hhalf1)
  -- (b) DGZ Lemma 3.2: `a^{(1/2)}_N ≤ exp(K₁ √(N log 2)) a^{(q)}_N`
  set K₁ : ℝ := (quantileConst q.toReal + quantileConst (2⁻¹ : ℝ≥0∞).toReal) * ξ with hK₁
  have hcmp : ∀ N, 1 ≤ N →
      aQ P₀ H₀ ξ N 2⁻¹ ≤ Real.exp (K₁ * √(N * Real.log 2)) * aQ P₀ H₀ ξ N q := by
    intro N hN
    have hab : (2 : ℝ)⁻¹ ^ N < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have h1 := (h₀.band N).lowerQuantile_lfppDistance_le_exp_mul hd0 h.kernel hW₀
      (by positivity) hab hξ (p₁ := q) (p₂ := 2⁻¹) hq0 hq1 hhalf0 hhalf1
    rw [log_one_div_inv_two_pow] at h1
    unfold aQ
    calc _ ≤ _ := h1
      _ = _ := by rw [hK₁]
  -- (c) large `N`
  have hbig : ∀ N, N₁ ≤ N →
      Real.exp (-(K₁ ^ 2 / (2 * ε))) * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * N) ≤ aQ P₀ H₀ ξ N q := by
    intro N hN
    have h1 := hcmp N (le_trans (le_max_right _ _) hN)
    have h2 := hmed N hN
    have h3 := exp_mul_sqrt_le K₁ hε N
    have hE0 := Real.exp_pos (K₁ * √(N * Real.log 2))
    have hq := hpos N q hq0 hq1
    have h4 : (2 : ℝ) ^ (-(1 - ξ * Q + ε / 2) * N) ≤
        Real.exp (K₁ ^ 2 / (2 * ε)) * (2 : ℝ) ^ (ε / 2 * N) * aQ P₀ H₀ ξ N q :=
      h2.trans (h1.trans (mul_le_mul_of_nonneg_right h3 hq.le))
    have e : (2 : ℝ) ^ (-(1 - ξ * Q + ε / 2) * N) =
        (2 : ℝ) ^ (ε / 2 * N) * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * N) := by
      rw [← Real.rpow_add two_pos]
      congr 1
      ring
    rw [e] at h4
    have h5 := Real.rpow_pos_of_pos (two_pos : (0 : ℝ) < 2) (ε / 2 * N)
    have h6 : (2 : ℝ) ^ (-(1 - ξ * Q + ε) * N) ≤
        Real.exp (K₁ ^ 2 / (2 * ε)) * aQ P₀ H₀ ξ N q := by
      have : (2 : ℝ) ^ (ε / 2 * N) * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * N) ≤
          (2 : ℝ) ^ (ε / 2 * N) * (Real.exp (K₁ ^ 2 / (2 * ε)) * aQ P₀ H₀ ξ N q) := by
        linarith
      exact le_of_mul_le_mul_left this h5
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    exact h6
  -- (d) small `N`: a positive minimum
  obtain ⟨m₀, -, hm₀⟩ := Finset.exists_min_image (Finset.range N₁)
    (fun m => aQ P₀ H₀ ξ m q * (2 : ℝ) ^ ((1 - ξ * Q + ε) * m))
    ⟨0, Finset.mem_range.2 (lt_of_lt_of_le zero_lt_one (le_max_right _ _))⟩
  set c₀ : ℝ := aQ P₀ H₀ ξ m₀ q * (2 : ℝ) ^ ((1 - ξ * Q + ε) * m₀) with hc₀
  have hc₀pos : 0 < c₀ := mul_pos (hpos m₀ q hq0 hq1) (Real.rpow_pos_of_pos two_pos _)
  refine ⟨min (Real.exp (-(K₁ ^ 2 / (2 * ε)))) c₀, lt_min (Real.exp_pos _) hc₀pos, fun N => ?_⟩
  have hpow0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 - ξ * Q + ε) * N) := Real.rpow_nonneg (by norm_num) _
  rcases lt_or_ge N N₁ with hN | hN
  · have h1 := hm₀ N (Finset.mem_range.2 hN)
    calc min (Real.exp (-(K₁ ^ 2 / (2 * ε)))) c₀ * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * N)
        ≤ c₀ * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * N) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpow0
      _ ≤ aQ P₀ H₀ ξ N q * (2 : ℝ) ^ ((1 - ξ * Q + ε) * N) *
            (2 : ℝ) ^ (-(1 - ξ * Q + ε) * N) := mul_le_mul_of_nonneg_right h1 hpow0
      _ = aQ P₀ H₀ ξ N q := by
          rw [mul_assoc, ← Real.rpow_add two_pos, show (1 - ξ * Q + ε) * (N : ℝ) +
            -(1 - ξ * Q + ε) * N = 0 by ring, Real.rpow_zero, mul_one]
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hpow0).trans (hbig N hN)

/-! ### The probability of `𝒜_{r,n}` -/

/-- **`P[𝒜_{r,n}ᶜ] ≤ C e^{-r/C}`** (MA7 D-4.3s, D-4.7s; from DGZ Lemma 4.2(1) = L3c1's
`lemma42_1` and a union bound over `r ≤ k < n`), with one `c₄ < 1` and one `C` for all
`q ∈ (c₄, 1)`, all dyadic realizations and all `1 ≤ r < n`. -/
theorem prob_eventA_compl_le (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ Q η : ℝ}
    (hξ : 0 < ξ) (hη : η < ξ * (Q - √(2 * d))) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∃ C > 0, ∀ q : ℝ≥0∞, c₄ < q → q < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ r n : ℕ, 1 ≤ r → r < n →
          P (eventA P H ξ Q η q r n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(r : ℝ) / C)) := by
  obtain ⟨c₄, hc₄, C₁, hC₁, hb⟩ := lemma42_1 hd hκ hξ hη
  set x : ℝ := Real.exp (-1 / C₁) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := Real.exp_lt_one_iff.2 (by rw [neg_div]; linarith [one_div_pos.2 hC₁])
  set C : ℝ := C₁ * (1 + 1 / (1 - x)) with hC
  have h1x : 0 < 1 - x := by linarith
  have hCC₁ : C₁ ≤ C := by
    rw [hC]
    have : 0 ≤ 1 / (1 - x) := by positivity
    nlinarith
  refine ⟨c₄, hc₄, C, by positivity, fun q hq hq1 Ω _ P W H hH r n hr hrn => ?_⟩
  obtain ⟨hG, -, hF⟩ := hb q hq hq1 hH
  have hsub : (eventA P H ξ Q η q r n)ᶜ ⊆
      (eventG ξ Q η H n)ᶜ ∪ ⋃ k ∈ Finset.Ico r n, (eventF P H ξ Q η q k n)ᶜ := by
    intro ω hω
    rw [mem_compl_iff, mem_eventA_iff] at hω
    by_cases hg : ω ∈ eventG ξ Q η H n
    · right
      have : ¬ ∀ k, r ≤ k → k < n → ω ∈ eventF P H ξ Q η q k n := fun h' => hω ⟨hg, h'⟩
      push Not at this
      obtain ⟨k, hk1, hk2, hk3⟩ := this
      exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_Ico.2 ⟨hk1, hk2⟩)) hk3
    · left
      exact hg
  have hexp_k : ∀ k : ℕ, Real.exp (-(k : ℝ) / C₁) = x ^ k := by
    intro k
    rw [hx, ← Real.exp_nat_mul]
    congr 1
    ring
  have hreal : C₁ * x ^ n + ∑ k ∈ Finset.Ico r n, C₁ * x ^ k ≤ C * Real.exp (-(r : ℝ) / C) := by
    have h1 : x ^ n ≤ x ^ r := pow_le_pow_of_le_one hx0.le hx1.le hrn.le
    have h2 := geom_sum_Ico_le_of_lt_one (m := r) (n := n) hx0.le hx1
    have h3 : x ^ r ≤ Real.exp (-(r : ℝ) / C) := by
      rw [← hexp_k]
      refine Real.exp_le_exp.2 ?_
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      rw [div_le_div_iff₀ hC₁ (by positivity)]
      nlinarith
    rw [← Finset.mul_sum]
    calc C₁ * x ^ n + C₁ * ∑ k ∈ Finset.Ico r n, x ^ k
        ≤ C₁ * x ^ r + C₁ * (x ^ r / (1 - x)) := by gcongr
      _ = C * x ^ r := by rw [hC]; field_simp
      _ ≤ C * Real.exp (-(r : ℝ) / C) := by gcongr
  calc P (eventA P H ξ Q η q r n)ᶜ
      ≤ P ((eventG ξ Q η H n)ᶜ ∪ ⋃ k ∈ Finset.Ico r n, (eventF P H ξ Q η q k n)ᶜ) :=
        measure_mono hsub
    _ ≤ P (eventG ξ Q η H n)ᶜ + P (⋃ k ∈ Finset.Ico r n, (eventF P H ξ Q η q k n)ᶜ) :=
        measure_union_le _ _
    _ ≤ P (eventG ξ Q η H n)ᶜ + ∑ k ∈ Finset.Ico r n, P (eventF P H ξ Q η q k n)ᶜ :=
        add_le_add le_rfl (measure_biUnion_finset_le _ _)
    _ ≤ ENNReal.ofReal (C₁ * Real.exp (-(n : ℝ) / C₁)) +
          ∑ k ∈ Finset.Ico r n, ENNReal.ofReal (C₁ * Real.exp (-(k : ℝ) / C₁)) := by
        refine add_le_add (hG n) (Finset.sum_le_sum fun k hk => ?_)
        rw [Finset.mem_Ico] at hk
        exact hF k n (by omega) hk.2
    _ = ENNReal.ofReal (C₁ * x ^ n + ∑ k ∈ Finset.Ico r n, C₁ * x ^ k) := by
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun k _ => by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), hexp_k]
        simp only [hexp_k]
    _ ≤ ENNReal.ofReal (C * Real.exp (-(r : ℝ) / C)) := ENNReal.ofReal_le_ofReal hreal

/-! ### The chaining sum against the quantile bound -/

/-- `2^{-(1-ξQ+η)k} 2^{-(1-ξQ-η/2)(n-k)} = (2^{-3η/2})^k 2^{-(1-ξQ-η/2)n}` for `k ≤ n`. -/
lemma two_rpow_mul_two_rpow_sub {ξ Q η : ℝ} {k n : ℕ} (hkn : k ≤ n) :
    (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * ((n - k : ℕ) : ℝ)) =
      ((2 : ℝ) ^ (-(3 * η / 2))) ^ k * (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * n) := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(3 * η / 2))) k, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add two_pos, ← Real.rpow_add two_pos, Nat.cast_sub hkn]
  congr 1
  ring

/-- **The chaining sum is `O(2^{-(1-ξQ-η/2)n})`** (MA7 D-4.7s): if `a^{(q)}_N ≤ A 2^{-(1-ξQ-η/2)N}`
for all `N` (`A ≥ 0`, `η > 0`), then
`chainSum r n ≤ (A + 1) S 2^{-(1-ξQ-η/2)n}` with `S = Σ_k k^{2d} (2^{-3η/2})^k`. -/
theorem chainSum_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℕ → Rd d → Ω → ℝ}
    {ξ Q η : ℝ} (hη : 0 < η) {q : ℝ≥0∞} {A : ℝ} (hA : 0 ≤ A)
    (haQ : ∀ N : ℕ, aQ P H ξ N q ≤ A * (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * N)) (r n : ℕ) :
    chainSum P H ξ Q η q r n ≤
      (A + 1) * (∑' k : ℕ, (k : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(3 * η / 2))) ^ k) *
        (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * n) := by
  set y : ℝ := (2 : ℝ) ^ (-(3 * η / 2)) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hsumm : Summable (fun k : ℕ => (k : ℝ) ^ (2 * d) * y ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one (2 * d)
      (by rw [Real.norm_eq_abs, abs_of_pos hy0]; exact hy1)
  set S : ℝ := ∑' k : ℕ, (k : ℝ) ^ (2 * d) * y ^ k with hS
  set T : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * n) with hT
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ k ∈ Finset.Ico r n,
      (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * aQ P H ξ (n - k) q ≤
        A * T * ((k : ℝ) ^ (2 * d) * y ^ k) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h1 := haQ (n - k)
    have h0 : 0 ≤ (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) := by positivity
    calc (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * aQ P H ξ (n - k) q
        ≤ (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) *
            (A * (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * ((n - k : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = A * (k : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(1 - ξ * Q + η) * k) *
            (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * ((n - k : ℕ) : ℝ))) := by ring
      _ = A * T * ((k : ℝ) ^ (2 * d) * y ^ k) := by
          rw [two_rpow_mul_two_rpow_sub hk.2.le]
          ring
  have hsum : ∑ k ∈ Finset.Ico r n, (k : ℝ) ^ (2 * d) * y ^ k ≤ S :=
    hsumm.sum_le_tsum _ (fun k _ => by positivity)
  have hlast : (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) =
      T * ((n : ℝ) ^ (2 * d) * y ^ n) := by
    have := two_rpow_mul_two_rpow_sub (ξ := ξ) (Q := Q) (η := η) (le_refl n)
    rw [Nat.sub_self, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at this
    rw [this, hT]
    ring
  have hlast' : (n : ℝ) ^ (2 * d) * y ^ n ≤ S := hsumm.le_tsum n (fun k _ => by positivity)
  unfold chainSum
  calc ∑ k ∈ Finset.Ico r n, (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) *
          aQ P H ξ (n - k) q + (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)
      ≤ ∑ k ∈ Finset.Ico r n, A * T * ((k : ℝ) ^ (2 * d) * y ^ k) +
          T * ((n : ℝ) ^ (2 * d) * y ^ n) := by
        rw [hlast]
        exact add_le_add (Finset.sum_le_sum hterm) le_rfl
    _ = A * T * ∑ k ∈ Finset.Ico r n, (k : ℝ) ^ (2 * d) * y ^ k +
          T * ((n : ℝ) ^ (2 * d) * y ^ n) := by rw [Finset.mul_sum]
    _ ≤ A * T * S + T * S := by
        gcongr
    _ = (A + 1) * S * T := by ring

/-- `2^{-(1-ξQ+η)k} 2^{-(1-ξQ-ε)(n-k)} = (2^{-(η+ε)})^k 2^{-(1-ξQ-ε)n}` for `k ≤ n`. -/
lemma two_rpow_mul_two_rpow_sub' {ξ Q η ε : ℝ} {k n : ℕ} (hkn : k ≤ n) :
    (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * (2 : ℝ) ^ (-(1 - ξ * Q - ε) * ((n - k : ℕ) : ℝ)) =
      ((2 : ℝ) ^ (-(η + ε))) ^ k * (2 : ℝ) ^ (-(1 - ξ * Q - ε) * n) := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(η + ε))) k, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add two_pos, ← Real.rpow_add two_pos, Nat.cast_sub hkn]
  congr 1
  ring

/-- **Tail form of the chaining sum** (for MA7 D-5.14 and D-6.1): if
`a^{(q)}_N ≤ A 2^{-(1-ξQ-ε)N}` for all `N` (`A ≥ 0`, `η + ε > 0`) and `j ≤ n`, then with
`y = 2^{-(η+ε)}`: `chainSum j n ≤ (A + 1)/(1 - y) · n^{2d} y^j 2^{-(1-ξQ-ε)n}`. -/
theorem chainSum_le_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H : ℕ → Rd d → Ω → ℝ} {ξ Q η ε : ℝ} (hηε : 0 < η + ε) {q : ℝ≥0∞} {A : ℝ} (hA : 0 ≤ A)
    (haQ : ∀ N : ℕ, aQ P H ξ N q ≤ A * (2 : ℝ) ^ (-(1 - ξ * Q - ε) * N)) {j n : ℕ} (hjn : j ≤ n) :
    chainSum P H ξ Q η q j n ≤
      (A + 1) / (1 - (2 : ℝ) ^ (-(η + ε))) * (n : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(η + ε))) ^ j *
        (2 : ℝ) ^ (-(1 - ξ * Q - ε) * n) := by
  set y : ℝ := (2 : ℝ) ^ (-(η + ε)) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have h1y : 0 < 1 - y := by linarith
  set T : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q - ε) * n) with hT
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  set M : ℝ := (n : ℝ) ^ (2 * d) with hM
  have hM0 : 0 ≤ M := by positivity
  have hterm : ∀ k ∈ Finset.Ico j n,
      (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * aQ P H ξ (n - k) q ≤
        A * T * M * y ^ k := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h1 := haQ (n - k)
    have h0 : 0 ≤ (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) := by positivity
    have hkM : (k : ℝ) ^ (2 * d) ≤ M := by
      rw [hM]
      gcongr
      exact_mod_cast hk.2.le
    calc (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * aQ P H ξ (n - k) q
        ≤ (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) *
            (A * (2 : ℝ) ^ (-(1 - ξ * Q - ε) * ((n - k : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = A * (k : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(1 - ξ * Q + η) * k) *
            (2 : ℝ) ^ (-(1 - ξ * Q - ε) * ((n - k : ℕ) : ℝ))) := by ring
      _ = A * T * ((k : ℝ) ^ (2 * d) * y ^ k) := by
          rw [two_rpow_mul_two_rpow_sub' hk.2.le]
          ring
      _ ≤ A * T * (M * y ^ k) := by gcongr
      _ = A * T * M * y ^ k := by ring
  have hgeom := geom_sum_Ico_le_of_lt_one (m := j) (n := n) hy0.le hy1
  have hlast : (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) = T * M * y ^ n := by
    have := two_rpow_mul_two_rpow_sub' (ξ := ξ) (Q := Q) (η := η) (ε := ε) (le_refl n)
    rw [Nat.sub_self, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at this
    rw [this, hT, hM]
    ring
  have hyn : y ^ n ≤ y ^ j / (1 - y) := by
    calc y ^ n ≤ y ^ j := pow_le_pow_of_le_one hy0.le hy1.le hjn
      _ ≤ y ^ j / (1 - y) := by
        rw [le_div_iff₀ h1y]
        have : 0 ≤ y ^ j * y := by positivity
        nlinarith
  unfold chainSum
  rw [hlast]
  calc ∑ k ∈ Finset.Ico j n, (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) *
          aQ P H ξ (n - k) q + T * M * y ^ n
      ≤ ∑ k ∈ Finset.Ico j n, A * T * M * y ^ k + T * M * y ^ n :=
        add_le_add (Finset.sum_le_sum hterm) le_rfl
    _ = A * T * M * ∑ k ∈ Finset.Ico j n, y ^ k + T * M * y ^ n := by rw [Finset.mul_sum]
    _ ≤ A * T * M * (y ^ j / (1 - y)) + T * M * (y ^ j / (1 - y)) := by
        have hATM : 0 ≤ A * T * M := by positivity
        have hTM : 0 ≤ T * M := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left hgeom hATM)
          (mul_le_mul_of_nonneg_left hyn hTM)
    _ = (A + 1) / (1 - y) * M * y ^ j * T := by
        field_simp

/-! ### Prop 4.7, upper half, self-internal form -/

/-- **MA7 D-4.7s for `B_ρ(0)`, `ρ ∈ [1, 3/2]`**: under `DGZHyp d κ ξ Q`, for every `δ > 0` there is
`C > 0` (one for all `ρ ∈ [1, 3/2]`) with
`P*[selfDiam_n(B_ρ(0)) > 2^{-(1-ξQ-δ)n}] ≤ C e^{-n/C}` for every dyadic realization and every
`n`. -/
theorem selfDiam_tail {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ ρ : ℝ, 1 ≤ ρ → ρ ≤ 3 / 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
        P {ω | (2 : ℝ) ^ (-(1 - ξ * Q - δ) * n) < selfDiam ξ (fun z => H n z ω) 0 ρ} ≤
          ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  have hd := h.dim
  have hκ := h.kernel
  have hξ := h.xi_pos
  have hgap : 0 < ξ * (Q - √(2 * d)) := mul_pos hξ (by linarith [h.subcritical])
  -- `η = min(δ, ξ(Q - √(2d)))/2`
  obtain ⟨η, hη0, hηgap, hηδ⟩ : ∃ η : ℝ, 0 < η ∧ η < ξ * (Q - √(2 * d)) ∧ η ≤ δ / 2 := by
    refine ⟨min δ (ξ * (Q - √(2 * d))) / 2, by positivity, ?_, ?_⟩
    · have := min_le_right δ (ξ * (Q - √(2 * d)))
      linarith
    · have := min_le_left δ (ξ * (Q - √(2 * d)))
      linarith
  obtain ⟨c₄, hc₄, C₁, hC₁, hAc⟩ := prob_eventA_compl_le hd hκ hξ hηgap
  obtain ⟨q, hqc, hq1⟩ := exists_between hc₄
  have hq0 : 0 < q := lt_of_le_of_lt (zero_le) hqc
  obtain ⟨A, hA0, haQ⟩ := exists_aQ_le h hq0 hq1 (ε := η / 2) (by positivity)
  obtain ⟨Cc, hCc, hchain⟩ := chain_selfInternal hd
  -- the series `S = Σ_k k^{2d} 2^{-3ηk/2}`
  obtain ⟨S, hS0, hS⟩ : ∃ S : ℝ, 0 ≤ S ∧
      ∑' k : ℕ, (k : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(3 * η / 2))) ^ k = S :=
    ⟨_, tsum_nonneg fun k => by positivity, rfl⟩
  -- the scale `r ≥ 110` with `P[𝒜_{r,n}ᶜ] ≤ 1/4`
  obtain ⟨r, hr110, hrC⟩ : ∃ r : ℕ, 110 ≤ r ∧ C₁ * Real.exp (-(r : ℝ) / C₁) ≤ 1 / 4 := by
    refine ⟨max 110 ⌈C₁ * Real.log (4 * C₁)⌉₊, le_max_left _ _, ?_⟩
    have h1 : C₁ * Real.log (4 * C₁) ≤ ((max 110 ⌈C₁ * Real.log (4 * C₁)⌉₊ : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    have h2 : -((max 110 ⌈C₁ * Real.log (4 * C₁)⌉₊ : ℕ) : ℝ) / C₁ ≤ -Real.log (4 * C₁) := by
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ hC₁]
      linarith
    calc C₁ * Real.exp (-((max 110 ⌈C₁ * Real.log (4 * C₁)⌉₊ : ℕ) : ℝ) / C₁)
        ≤ C₁ * Real.exp (-Real.log (4 * C₁)) := by gcongr
      _ = 1 / 4 := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  -- the level of the `3/4`-quantile: `K 2^{-(1-ξQ-η/2)n}`
  obtain ⟨K, hK0, hKge⟩ : ∃ K : ℝ, 0 < K ∧ Cc * 2 ^ r * ((A + 1) * S) ≤ K := by
    refine ⟨Cc * 2 ^ r * ((A + 1) * S) + 1, ?_, by linarith⟩
    have : 0 ≤ Cc * 2 ^ r * ((A + 1) * S) := by positivity
    linarith
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, Real.log 2 = L := ⟨_, rfl⟩
  rw [hLdef] at hL
  obtain ⟨c, hc0, hcdef⟩ : ∃ c : ℝ, 0 ≤ c ∧ quantileConst (3 / 4) = c :=
    ⟨_, HigherDimLFPP.Conc.quantileConst_nonneg _, rfl⟩
  -- `n ≥ n₁`: `n log 2 ≥ 4 |log K|/δ + (4 ξ c/δ)²`
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, ∀ m : ℕ, n₁ ≤ m →
      4 * |Real.log K| / δ + (4 * ξ * c / δ) ^ 2 ≤ m * L := by
    refine ⟨⌈(4 * |Real.log K| / δ + (4 * ξ * c / δ) ^ 2) / L⌉₊, fun m hm => ?_⟩
    have h1 : (4 * |Real.log K| / δ + (4 * ξ * c / δ) ^ 2) / L ≤ m :=
      (Nat.le_ceil _).trans (by exact_mod_cast hm)
    rwa [div_le_iff₀ hL] at h1
  -- the rate `β = δ² log 2/(32 ξ²)` and the constant `C`
  obtain ⟨β, hβ0, hβ⟩ : ∃ β : ℝ, 0 < β ∧ δ ^ 2 * L / (32 * ξ ^ 2) = β :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨C, hC1, hC2, hC3⟩ : ∃ C : ℝ, ((max r n₁ : ℕ) : ℝ) + 1 ≤ C ∧ 2 ≤ C ∧ 1 / β ≤ C :=
    ⟨max (((max r n₁ : ℕ) : ℝ) + 1) (max 2 (1 / β)), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, fun ρ hρ1 hρ2 Ω _ P W H hH n => ?_⟩
  have hW := hH.whiteNoise
  have hP := hW.isProbabilityMeasure
  rcases le_or_gt n (max r n₁) with hn | hn
  · -- small `n`: the probability is at most `1 ≤ C e^{-n/C}`
    calc P {ω | (2 : ℝ) ^ (-(1 - ξ * Q - δ) * n) < selfDiam ξ (fun z => H n z ω) 0 ρ}
        ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
        refine ENNReal.ofReal_le_ofReal (one_le_mul_exp_neg_div (Nat.cast_nonneg n) ?_)
        have : (n : ℝ) ≤ ((max r n₁ : ℕ) : ℝ) := by exact_mod_cast hn
        linarith
  -- large `n`
  have hrn : r < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : n₁ ≤ n := (le_max_right r n₁).trans hn.le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hrn)
  obtain ⟨T, hT0, hTdef⟩ : ∃ T : ℝ, 0 < T ∧ K * (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * n) = T :=
    ⟨_, mul_pos hK0 (Real.rpow_pos_of_pos two_pos _), rfl⟩
  -- (1) `𝒜_{r,n}` has probability `≥ 3/4` and lies in `{selfDiam ≤ T}`
  have hA14 : P (eventA P H ξ Q η q r n)ᶜ ≤ ENNReal.ofReal (1 / 4) :=
    (hAc q hqc hq1 hH r n (by omega) hrn).trans (ENNReal.ofReal_le_ofReal hrC)
  have hA34 : ENNReal.ofReal (3 / 4) ≤ P (eventA P H ξ Q η q r n) := by
    have h1 : (1 : ℝ≥0∞) ≤ P (eventA P H ξ Q η q r n) + P (eventA P H ξ Q η q r n)ᶜ := by
      rw [← measure_univ (μ := P), ← union_compl_self (eventA P H ξ Q η q r n)]
      exact measure_union_le _ _
    have h2 : ENNReal.ofReal (3 / 4) + ENNReal.ofReal (1 / 4) = 1 := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    refine ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (1 / 4)) ENNReal.ofReal_ne_top ?_
    calc ENNReal.ofReal (3 / 4) + ENNReal.ofReal (1 / 4) = 1 := h2
      _ ≤ P (eventA P H ξ Q η q r n) + P (eventA P H ξ Q η q r n)ᶜ := h1
      _ ≤ P (eventA P H ξ Q η q r n) + ENNReal.ofReal (1 / 4) := add_le_add le_rfl hA14
  have hsub : eventA P H ξ Q η q r n ⊆ {ω | selfDiam ξ (fun z => H n z ω) 0 ρ ≤ T} := by
    intro ω hω
    have h1 := (hchain P H ξ Q η q r n ρ ω hξ hr110 hrn hρ1 hρ2 ((hH.band n).continuous ω)
      hω).2
    have h2 := chainSum_le (P := P) (H := H) (ξ := ξ) (Q := Q) hη0 (q := q) hA0.le
      (haQ Ω P W H hH) r n
    rw [hS] at h2
    have hT2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * n) :=
      Real.rpow_nonneg (by norm_num) _
    show selfDiam ξ (fun z => H n z ω) 0 ρ ≤ T
    calc selfDiam ξ (fun z => H n z ω) 0 ρ ≤ Cc * 2 ^ r * chainSum P H ξ Q η q r n := h1
      _ ≤ Cc * 2 ^ r * ((A + 1) * S * (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * n)) := by gcongr
      _ = Cc * 2 ^ r * ((A + 1) * S) * (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * n) := by ring
      _ ≤ K * (2 : ℝ) ^ (-(1 - ξ * Q - η / 2) * n) := mul_le_mul_of_nonneg_right hKge hT2
      _ = T := hTdef
  have hprob : ENNReal.ofReal (3 / 4) ≤
      P {ω | (fun φ => selfDiam ξ φ 0 ρ) (fun z => H n z ω) ≤ T} :=
    hA34.trans (measure_mono hsub)
  -- (2) concentration (MA7 D-4.6): `E log selfDiam < log T + ξ √(n log 2) c`
  have hX := hH.band n
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hab : (2 : ℝ)⁻¹ ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hKc : IsCompact (cbox (0 : Rd d) ρ) := isCompact_cbox 0 ρ
  have hρ0 : 0 < ρ := by linarith
  have hΦ := isSupLipschitzOn_log_selfDiam (d := d) ξ (0 : Rd d) hρ0
  have hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < selfDiam ξ φ 0 ρ :=
    fun φ hφ => selfDiam_pos (by omega) hφ hρ0
  have hint := integral_log_lt_log_add_of_le_measure_le hκ hW ha hab hX hKc hξ.ne'
    (Φ := fun φ => selfDiam ξ φ 0 ρ) hΦ hpos hT0 (p := 3 / 4) (by norm_num) (by norm_num) hprob
  rw [log_one_div_inv_two_pow, abs_of_pos hξ, hLdef, hcdef] at hint
  -- (3) the tail at `T' = 2^{-(1-ξQ-δ)n}` with `t = (δ/4) n log 2`
  obtain ⟨T', hT'0, hT'def⟩ : ∃ T' : ℝ, 0 < T' ∧ (2 : ℝ) ^ (-(1 - ξ * Q - δ) * n) = T' :=
    ⟨_, Real.rpow_pos_of_pos two_pos _, rfl⟩
  have ht0 : 0 ≤ δ / 4 * (n * L) := by positivity
  have hlogT : Real.log T = Real.log K + -(1 - ξ * Q - η / 2) * n * L := by
    rw [← hTdef, Real.log_mul hK0.ne' (Real.rpow_pos_of_pos two_pos _).ne', Real.log_rpow two_pos,
      hLdef]
  have hlogT' : Real.log T' = -(1 - ξ * Q - δ) * n * L := by
    rw [← hT'def, Real.log_rpow two_pos, hLdef]
  -- `n ≥ n₁`: `log K + ξ c √(n log 2) ≤ (δ/2) n log 2`
  have hbig : Real.log K + ξ * √(n * L) * c ≤ δ / 2 * (n * L) := by
    have hn1' := hn₁ n hn1
    obtain ⟨u, hudef⟩ : ∃ u : ℝ, √(n * L) = u := ⟨_, rfl⟩
    have hu2 : u ^ 2 = n * L := by rw [← hudef]; exact Real.sq_sqrt (by positivity)
    have hu0 : 0 ≤ u := by rw [← hudef]; exact Real.sqrt_nonneg _
    rw [hudef]
    have hA1 : 4 * |Real.log K| / δ ≤ u ^ 2 := by
      rw [hu2]
      have : 0 ≤ (4 * ξ * c / δ) ^ 2 := sq_nonneg _
      linarith only [hn1', this]
    have hA2 : 4 * ξ * c / δ ≤ u := by
      have h0 : 0 ≤ 4 * ξ * c / δ := by positivity
      rw [← Real.sqrt_sq h0, ← Real.sqrt_sq hu0]
      refine Real.sqrt_le_sqrt ?_
      have : 0 ≤ 4 * |Real.log K| / δ := by positivity
      rw [hu2]
      linarith only [hn1', this]
    have hB1 : |Real.log K| ≤ δ / 4 * u ^ 2 := by
      rw [div_le_iff₀ hδ] at hA1
      linarith only [hA1]
    have hB2 : ξ * u * c ≤ δ / 4 * u ^ 2 := by
      have h1 : ξ * c ≤ δ / 4 * u := by
        rw [div_le_iff₀ hδ] at hA2
        linarith only [hA2]
      have := mul_le_mul_of_nonneg_right h1 hu0
      linarith only [this]
    have hB3 := le_abs_self (Real.log K)
    rw [hu2] at hB1 hB2
    linarith only [hB1, hB2, hB3]
  have hle : ∫ ω, Real.log ((fun φ => selfDiam ξ φ 0 ρ) fun z => H n z ω) ∂P +
      δ / 4 * (n * L) ≤ Real.log T' := by
    rw [hlogT']
    rw [hlogT] at hint
    have hδη : η / 2 ≤ δ / 4 := by linarith only [hηδ]
    have h1 : (η / 2) * (n * L) ≤ (δ / 4) * (n * L) :=
      mul_le_mul_of_nonneg_right hδη (by positivity)
    have e1 : -(1 - ξ * Q - η / 2) * n * L = -(1 - ξ * Q) * (n * L) + η / 2 * (n * L) := by ring
    have e2 : -(1 - ξ * Q - δ) * n * L = -(1 - ξ * Q) * (n * L) + δ * (n * L) := by ring
    rw [e1] at hint
    rw [e2]
    linarith only [hint, hbig, h1]
  have htail := measure_lt_le_of_integral_log_add_le hκ hW ha hab.le hX hKc
    (Φ := fun φ => selfDiam ξ φ 0 ρ) hΦ hT'0 ht0 hle
  rw [log_one_div_inv_two_pow, hLdef] at htail
  -- (4) `2 exp(-t²/(2 ξ² n log 2)) = 2 exp(-β n) ≤ C e^{-n/C}`
  have hexpo : -(δ / 4 * (n * L)) ^ 2 / (2 * ξ ^ 2 * (n * L)) = -(β * n) := by
    rw [← hβ]
    field_simp
    ring
  rw [hexpo] at htail
  rw [← hT'def] at htail
  refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : Real.exp (-(β * n)) ≤ Real.exp (-(n : ℝ) / C) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hCpos]
    have : 1 ≤ β * C := by
      rw [div_le_iff₀ hβ0] at hC3
      linarith only [hC3]
    have h2 : (n : ℝ) * 1 ≤ n * (β * C) := mul_le_mul_of_nonneg_left this hnpos.le
    linarith only [h2]
  have h2 := Real.exp_pos (-(n : ℝ) / C)
  have h3 := Real.exp_pos (-(β * n))
  have h4 : 2 * Real.exp (-(n : ℝ) / C) ≤ C * Real.exp (-(n : ℝ) / C) :=
    mul_le_mul_of_nonneg_right hC2 h2.le
  linarith only [h1, h4]

/-- **MA7 Details (c) `SelfDiamShape`** (DGZ Prop 4.7, upper half, self-internal form;
MA7 D-4.7s), for every `d, κ, ξ, Q`. -/
theorem selfDiamShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : SelfDiamShape d κ ξ Q := by
  intro h δ hδ
  obtain ⟨C, hC, hb⟩ := selfDiam_tail h hδ
  exact ⟨C, hC, fun Ω _ P W H hH n => hb 1 le_rfl (by norm_num) Ω P W H hH n⟩

end DGZ

end HigherDimLQGMetric
