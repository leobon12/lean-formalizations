import HigherDimLQGContinuity.Unif4.Sec42
import HigherDimLQGContinuity.Unif4.Quant

/-!
# Uniform self-internal diameter tail: upper half of DGZ Prop 4.7 (packet U1)

Blueprint Part D, `d:prop-u47` (NA3 §2.3, ROUTE-3; [8]-bp `r2:prop:47s`). Port of
`HigherDimLQGMetric.DGZ.selfDiam_tail` (`DGZ/SelfDiam.lean`, MA7 D-4.7s).

**Statement** (`selfDiam_tail_unif`). Let `d ≥ 2`, `κ` admissible, `b, μ, δ > 0`. There is `C = C(d, κ, b, μ, δ) > 0`
such that for every `ξ` with `UHyp d κ b μ ξ`, every centre `c`, every `ρ ∈ [1, 3/2]`, every dyadic realization and
every `n`, `P*[selfDiam_n(B_ρ(c)) > 2^{-(1-ξQ(ξ)-δ)n}] ≤ C e^{-n/C}`. The centre-`0` case is
`u1_selfDiam_tail_zero`; a general centre follows by translation invariance in law (`DGZ.map_selfDiam_sim_eq`, `r = 1`).

**Proof** (the proof of `DGZ.selfDiam_tail` with uniform constants):
* the margin is `η = min(δ, μ)/2` instead of `min(δ, ξ(Q - √(2d)))/2` (`η < μ ≤ gap(ξ)`, `d:lem-consts`(i));
* `q ∈ (c₄, 1)` with the uniform `c₄ = c₄(d, κ)` and `P[𝒜_{r,n}ᶜ] ≤ C₁ e^{-r/C₁}` from `prob_eventA_compl_le_unif`;
* `a^{(q)}_N ≤ A 2^{-(1-ϕ-η/2)N}` for all `N` from `exists_aQ_le_unif` (U-EXP);
* the chaining (`DGZ.chain_selfInternal`, `DGZ.chainSum_le`) is deterministic and reused;
* in the concentration step the variance proxy is `ξ² n log 2 ≤ b² n log 2`: the threshold `n₁` uses
  `(4bc/δ)²` instead of `(4ξc/δ)²`, and the rate is `β = δ² log 2/(32 b²) ≤ δ² log 2/(32 ξ²)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)
open HigherDimLFPP.Conc (quantileConst)

variable {d : ℕ}

/-- **Uniform DGZ Prop 4.7, upper half, self-internal form, centre `0`** (port of `DGZ.selfDiam_tail`): for
`d ≥ 2`, `κ` admissible and `b, μ, δ > 0` there is `C > 0` (depending only on `d, κ, b, μ, δ`) such that for every
`ξ` with `UHyp d κ b μ ξ`, every `ρ ∈ [1, 3/2]`, every dyadic realization and every `n`,
`P*[selfDiam_n(B_ρ(0)) > 2^{-(1-ξQ(ξ)-δ)n}] ≤ C e^{-n/C}`. Every centre: `selfDiam_tail_unif`. -/
theorem u1_selfDiam_tail_zero (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ ρ : ℝ, 1 ≤ ρ → ρ ≤ 3 / 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | (2 : ℝ) ^ (-(1 - ξ * distExp d ξ - δ) * n) < selfDiam ξ (fun z => H n z ω) 0 ρ} ≤
            ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  -- the uniform margin `η = min(δ, μ)/2`
  obtain ⟨η, hη0, hημ, hηδ⟩ : ∃ η : ℝ, 0 < η ∧ η < μ ∧ η ≤ δ / 2 := by
    refine ⟨min δ μ / 2, by positivity, ?_, ?_⟩
    · have := min_le_right δ μ
      linarith
    · have := min_le_left δ μ
      linarith
  obtain ⟨c₄, hc₄, hAunif⟩ := prob_eventA_compl_le_unif hd hκ
  obtain ⟨C₁, hC₁, hAc⟩ := hAunif b μ η hημ
  obtain ⟨q, hqc, hq1⟩ := exists_between hc₄
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hqc
  obtain ⟨A, hA0, haQ⟩ := exists_aQ_le_unif hd hκ hb hq0 hq1 (ε := η / 2) (by positivity)
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
  -- `n ≥ n₁`: `n log 2 ≥ 4 |log K|/δ + (4 b c/δ)²` (uniform: `ξ ≤ b`)
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, ∀ m : ℕ, n₁ ≤ m →
      4 * |Real.log K| / δ + (4 * b * c / δ) ^ 2 ≤ m * L := by
    refine ⟨⌈(4 * |Real.log K| / δ + (4 * b * c / δ) ^ 2) / L⌉₊, fun m hm => ?_⟩
    have h1 : (4 * |Real.log K| / δ + (4 * b * c / δ) ^ 2) / L ≤ m :=
      (Nat.le_ceil _).trans (by exact_mod_cast hm)
    rwa [div_le_iff₀ hL] at h1
  -- the uniform rate `β = δ² log 2/(32 b²)` and the constant `C`
  obtain ⟨β, hβ0, hβ⟩ : ∃ β : ℝ, 0 < β ∧ δ ^ 2 * L / (32 * b ^ 2) = β :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨C, hC1, hC2, hC3⟩ : ∃ C : ℝ, ((max r n₁ : ℕ) : ℝ) + 1 ≤ C ∧ 2 ≤ C ∧ 1 / β ≤ C :=
    ⟨max (((max r n₁ : ℕ) : ℝ) + 1) (max 2 (1 / β)), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, fun ξ hξh ρ hρ1 hρ2 Ω _ P W H hH n => ?_⟩
  have hξ : 0 < ξ := hξh.base.xi_pos
  have hξb : ξ ≤ b := hξh.le_b
  have hgap : μ ≤ ξ * (distExp d ξ - √(2 * d)) := hξh.gap
  set Q : ℝ := distExp d ξ with hQ
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
    (hAc ξ Q hξ hξb hgap q hqc hq1 hH r n (by omega) hrn).trans (ENNReal.ofReal_le_ofReal hrC)
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
      (haQ ξ hξ hξb Ω P W H hH) r n
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
      have : 0 ≤ (4 * b * c / δ) ^ 2 := sq_nonneg _
      linarith only [hn1', this]
    have hA2 : 4 * b * c / δ ≤ u := by
      have h0 : 0 ≤ 4 * b * c / δ := by positivity
      rw [← Real.sqrt_sq h0, ← Real.sqrt_sq hu0]
      refine Real.sqrt_le_sqrt ?_
      have : 0 ≤ 4 * |Real.log K| / δ := by positivity
      rw [hu2]
      linarith only [hn1', this]
    have hξc : 4 * ξ * c / δ ≤ 4 * b * c / δ := by
      have : 4 * ξ * c ≤ 4 * b * c := by
        have := mul_le_mul_of_nonneg_right hξb hc0
        linarith
      exact div_le_div_of_nonneg_right this hδ.le
    have hB1 : |Real.log K| ≤ δ / 4 * u ^ 2 := by
      rw [div_le_iff₀ hδ] at hA1
      linarith only [hA1]
    have hB2 : ξ * u * c ≤ δ / 4 * u ^ 2 := by
      have h1 : ξ * c ≤ δ / 4 * u := by
        have h3 := hξc.trans hA2
        rw [div_le_iff₀ hδ] at h3
        linarith only [h3]
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
  -- (4) `2 exp(-t²/(2 ξ² n log 2)) ≤ 2 exp(-β n) ≤ C e^{-n/C}` (`ξ ≤ b`)
  have hexpo : -(δ / 4 * (n * L)) ^ 2 / (2 * ξ ^ 2 * (n * L)) ≤ -(β * n) := by
    rw [← hβ, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have hξ2 : ξ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hξ.le hξb 2
    have e : δ ^ 2 * L / (32 * b ^ 2) * n * (2 * ξ ^ 2 * (n * L)) =
        (δ / 4 * (n * L)) ^ 2 * (ξ ^ 2 / b ^ 2) := by
      field_simp
      ring
    rw [e]
    have h1 : ξ ^ 2 / b ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hξ2
    have h0 : 0 ≤ (δ / 4 * (n * L)) ^ 2 := sq_nonneg _
    nlinarith
  rw [← hT'def] at htail
  refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : Real.exp (-(δ / 4 * (n * L)) ^ 2 / (2 * ξ ^ 2 * (n * L))) ≤
      Real.exp (-(n : ℝ) / C) := by
    refine Real.exp_le_exp.2 (hexpo.trans ?_)
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hCpos]
    have : 1 ≤ β * C := by
      rw [div_le_iff₀ hβ0] at hC3
      linarith only [hC3]
    have h2 : (n : ℝ) * 1 ≤ n * (β * C) := mul_le_mul_of_nonneg_left this hnpos.le
    linarith only [h2]
  have h2 := Real.exp_pos (-(n : ℝ) / C)
  have h4 : 2 * Real.exp (-(n : ℝ) / C) ≤ C * Real.exp (-(n : ℝ) / C) :=
    mul_le_mul_of_nonneg_right hC2 h2.le
  linarith only [h1, h4]

/-- **Uniform DGZ Prop 4.7, upper half, self-internal form** (`d:prop-u47`; port of `DGZ.selfDiam_tail`, every
centre): for `d ≥ 2`, `κ` admissible and `b, μ, δ > 0` there is `C > 0` (depending only on `d, κ, b, μ, δ`) such that
for every `ξ` with `UHyp d κ b μ ξ`, every centre `c`, every `ρ ∈ [1, 3/2]`, every dyadic realization and every `n`,
`P*[selfDiam_n(B_ρ(c)) > 2^{-(1-ξQ(ξ)-δ)n}] ≤ C e^{-n/C}` (translation invariance in law,
`DGZ.map_selfDiam_sim_eq` with `r = 1`, reduces it to the centre `0`). -/
theorem selfDiam_tail_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ (c : Rd d) (ρ : ℝ), 1 ≤ ρ → ρ ≤ 3 / 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | (2 : ℝ) ^ (-(1 - ξ * distExp d ξ - δ) * n) < selfDiam ξ (fun z => H n z ω) c ρ} ≤
            ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  obtain ⟨C, hC, h0⟩ := u1_selfDiam_tail_zero hd hκ hb hμ hδ
  refine ⟨C, hC, fun ξ hξ c ρ hρ1 hρ2 Ω _ P W H hH n => ?_⟩
  have hW := hH.whiteNoise
  have hX := hH.band n
  have hX' : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n / 1) (1 / 1) (H n) :=
    hX.congr_band (div_one _).symm (div_one _).symm
  have hmap := map_selfDiam_sim_eq hX hX' hW hW hκ c one_pos (by positivity) ξ 0 ρ
  simp only [smul_zero, add_zero, one_mul] at hmap
  have hF : Measurable fun ω => selfDiam ξ (fun z => H n z ω) c ρ :=
    measurable_selfDiam hX.continuous hX.measurable ξ c ρ
  have hF' : Measurable fun ω => selfDiam ξ (fun z => H n z ω) 0 ρ :=
    measurable_selfDiam hX.continuous hX.measurable ξ 0 ρ
  rw [measure_lt_eq_of_map_eq hF hF' hmap]
  exact h0 ξ hξ ρ hρ1 hρ2 Ω P W H hH n

/-- **The `B₁(0)` form** (port of `DGZ.selfDiamShape`): `selfDiam_tail_unif` at `(c, ρ) = (0, 1)`. -/
theorem selfDiamShape_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | (2 : ℝ) ^ (-(1 - ξ * distExp d ξ - δ) * n) < selfDiam ξ (fun z => H n z ω) 0 1} ≤
            ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  obtain ⟨C, hC, hb'⟩ := u1_selfDiam_tail_zero hd hκ hb hμ hδ
  exact ⟨C, hC, fun ξ hξ Ω _ P W H hH n => hb' ξ hξ 1 le_rfl (by norm_num) Ω P W H hH n⟩

end HigherDimLQGContinuity
