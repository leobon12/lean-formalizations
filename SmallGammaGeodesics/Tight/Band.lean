import SmallGammaGeodesics.Tight.Coord

/-!
# §6: the band event at the scale `Kδ` from Lemma 5.1 (packet P-T1)

Blueprint `blueprint/sections/s6-tightness.tex`, Lemma `lem:band-event-K` (source (6.3)–(6.4)); statements of
`planning/packets/BP2-planned-statements.md` (§6 block, `bandEv_scale_le`).

Lemma `lem:band-event-K` is Lemma 5.1 (`lemma51`, packet P-U3) at `R = Kδ` together with the mean bound
`m = E M ≤ C₆ δ` (`mean_maxDev_le`, packet P-U3). This file proves the reduction
`bandEv_scale_le_of_lemma51`: its two hypotheses are, verbatim, the planned conclusions of `lemma51` and
`mean_maxDev_le` (BP2 §5 block), and its conclusion is, verbatim, the planned conclusion of `bandEv_scale_le`.
The target `bandEv_scale_le` itself is `bandEv_scale_le_of_lemma51 G (lemma51 G hCC h42) (mean_maxDev_le G hCC h42)`
once P-U3 has landed.

The exponent bookkeeping (blueprint, proof of `lem:band-event-K`; `ξ² = δ³`):
* `ξ²/(Kδ)³ = K^{-3}`;
* `ξ² (m + ξ^{99/100} L)/(Kδ)⁴ = (m + ξ^{99/100} L)/(K⁴ δ) ≤ C₆ K^{-4} + ξ^{97/300} L`;
* `ξ^{49/32} L²/(Kδ)² = ξ^{19/96} L²/K² ≤ ξ^{19/96} L²` (as `49/32 = 19/96 + 4/3`);
* the remainder `ξ^{97/300} L + ξ^{19/96} L² ≤ (600/97) ξ^{97/600} + (384/19)² ξ^{19/192}` tends to `0`
  (`log(1/ξ) ≤ ξ^{-q}/q`, `Real.log_le_rpow_div`);
* `Kδ ≤ 2 ξ^{99/200}` as soon as `K ξ^{103/600} ≤ 2` (`2/3 − 99/200 = 103/600`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## The right side of Lemma 5.1 at `R = Kδ` -/

/-- `(ξ^{2/3})³ = ξ²`. -/
theorem Tight.rpow_two_thirds_pow_three {ξ : ℝ} (hξ : 0 ≤ ξ) : (ξ ^ (2 / 3 : ℝ)) ^ 3 = ξ ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hξ, ← Real.rpow_natCast]
  norm_num

/-- **The right side of Lemma 5.1 at `R = Kδ`** (blueprint, proof of `lem:band-event-K`): for `ξ > 0`, `K ≥ 1`,
`δ = ξ^{2/3}`, `m ≤ C₆ δ` and `L ≥ 0`,
`ξ²/(Kδ)³ + ξ²(m + ξ^{99/100} L)/(Kδ)⁴ + ξ^{49/32} L²/(Kδ)² ≤ K^{-3} + C₆ K^{-4} + (ξ^{97/300} L + ξ^{19/96} L²)`. -/
theorem Tight.lemma51_rhs_le {ξ K m L C₆ : ℝ} (hξ : 0 < ξ) (hK : 1 ≤ K)
    (hm : m ≤ C₆ * ξ ^ (2 / 3 : ℝ)) (hL : 0 ≤ L) :
    ξ ^ 2 / (K * ξ ^ (2 / 3 : ℝ)) ^ 3 +
        ξ ^ 2 * (m + ξ ^ (99 / 100 : ℝ) * L) / (K * ξ ^ (2 / 3 : ℝ)) ^ 4 +
        ξ ^ (49 / 32 : ℝ) * L ^ 2 / (K * ξ ^ (2 / 3 : ℝ)) ^ 2 ≤
      K ^ (-3 : ℝ) + C₆ * K ^ (-4 : ℝ) + (ξ ^ (97 / 300 : ℝ) * L + ξ ^ (19 / 96 : ℝ) * L ^ 2) := by
  set δ : ℝ := ξ ^ (2 / 3 : ℝ) with hδ
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hξ _
  have hK0 : 0 < K := by linarith
  have hξ2 : ξ ^ 2 = δ ^ 3 := (Tight.rpow_two_thirds_pow_three hξ.le).symm
  have hK3 : K ^ (-3 : ℝ) = (K ^ 3)⁻¹ := by
    rw [Real.rpow_neg hK0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hK4 : K ^ (-4 : ℝ) = (K ^ 4)⁻¹ := by
    rw [Real.rpow_neg hK0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hK41 : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hK21 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have ha : ξ ^ (99 / 100 : ℝ) = ξ ^ (97 / 300 : ℝ) * δ := Tight.rpow_ninetyNine_hundredths_eq hξ
  have hb : ξ ^ (49 / 32 : ℝ) = ξ ^ (19 / 96 : ℝ) * δ ^ 2 := by
    rw [hδ, ← Real.rpow_natCast, ← Real.rpow_mul hξ.le, ← Real.rpow_add hξ]
    norm_num
  have he1 : 0 ≤ ξ ^ (97 / 300 : ℝ) := Real.rpow_nonneg hξ.le _
  have he2 : 0 ≤ ξ ^ (19 / 96 : ℝ) := Real.rpow_nonneg hξ.le _
  -- the three terms
  have t1 : ξ ^ 2 / (K * δ) ^ 3 = K ^ (-3 : ℝ) := by
    rw [hK3, hξ2, mul_pow]
    field_simp
  have t2 : ξ ^ 2 * (m + ξ ^ (99 / 100 : ℝ) * L) / (K * δ) ^ 4 ≤
      C₆ * K ^ (-4 : ℝ) + ξ ^ (97 / 300 : ℝ) * L := by
    have e : ξ ^ 2 * (m + ξ ^ (99 / 100 : ℝ) * L) / (K * δ) ^ 4 =
        m / δ * (K ^ 4)⁻¹ + ξ ^ (97 / 300 : ℝ) * L * (K ^ 4)⁻¹ := by
      rw [hξ2, ha, mul_pow]
      field_simp
    rw [e, hK4]
    have h1 : m / δ ≤ C₆ := by
      rw [div_le_iff₀ hδ0]
      linarith
    have hKi : (K ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK41
    have hKi0 : 0 ≤ (K ^ 4)⁻¹ := by positivity
    have h2 : ξ ^ (97 / 300 : ℝ) * L * (K ^ 4)⁻¹ ≤ ξ ^ (97 / 300 : ℝ) * L := by
      have : 0 ≤ ξ ^ (97 / 300 : ℝ) * L := mul_nonneg he1 hL
      calc ξ ^ (97 / 300 : ℝ) * L * (K ^ 4)⁻¹ ≤ ξ ^ (97 / 300 : ℝ) * L * 1 :=
            mul_le_mul_of_nonneg_left hKi this
        _ = ξ ^ (97 / 300 : ℝ) * L := mul_one _
    have h3 : m / δ * (K ^ 4)⁻¹ ≤ C₆ * (K ^ 4)⁻¹ := mul_le_mul_of_nonneg_right h1 hKi0
    linarith
  have t3 : ξ ^ (49 / 32 : ℝ) * L ^ 2 / (K * δ) ^ 2 ≤ ξ ^ (19 / 96 : ℝ) * L ^ 2 := by
    have e : ξ ^ (49 / 32 : ℝ) * L ^ 2 / (K * δ) ^ 2 = ξ ^ (19 / 96 : ℝ) * L ^ 2 / K ^ 2 := by
      rw [hb, mul_pow]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have : 0 ≤ ξ ^ (19 / 96 : ℝ) * L ^ 2 := by positivity
    nlinarith
  linarith

/-- The remainder of `lem:band-event-K` is small: for `0 < ξ ≤ 1`, with `L = log(1/ξ)`,
`ξ^{97/300} L ≤ (600/97) ξ^{97/600}` and `ξ^{19/96} L² ≤ (384/19)² ξ^{19/192}` (from
`log x ≤ x^q/q`, `Real.log_le_rpow_div`). -/
theorem Tight.rpow_mul_log_inv_le {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ξ ^ (97 / 300 : ℝ) * Real.log ξ⁻¹ ≤ 600 / 97 * ξ ^ (97 / 600 : ℝ) ∧
      ξ ^ (19 / 96 : ℝ) * Real.log ξ⁻¹ ^ 2 ≤ (384 / 19) ^ 2 * ξ ^ (19 / 192 : ℝ) := by
  have hL0 : 0 ≤ Real.log ξ⁻¹ := Real.log_nonneg ((one_le_inv₀ hξ).2 hξ1)
  have hinv : ∀ q : ℝ, ξ⁻¹ ^ q = ξ ^ (-q) := fun q => by
    rw [Real.inv_rpow hξ.le, ← Real.rpow_neg hξ.le]
  constructor
  · have hlog := Real.log_le_rpow_div (inv_nonneg.2 hξ.le) (by norm_num : (0 : ℝ) < 97 / 600)
    rw [hinv] at hlog
    have he : 0 ≤ ξ ^ (97 / 300 : ℝ) := Real.rpow_nonneg hξ.le _
    calc ξ ^ (97 / 300 : ℝ) * Real.log ξ⁻¹
        ≤ ξ ^ (97 / 300 : ℝ) * (ξ ^ (-(97 / 600 : ℝ)) / (97 / 600)) :=
          mul_le_mul_of_nonneg_left hlog he
      _ = 600 / 97 * (ξ ^ (97 / 300 : ℝ) * ξ ^ (-(97 / 600 : ℝ))) := by ring
      _ = 600 / 97 * ξ ^ (97 / 600 : ℝ) := by
          rw [← Real.rpow_add hξ]
          norm_num
  · have hlog := Real.log_le_rpow_div (inv_nonneg.2 hξ.le) (by norm_num : (0 : ℝ) < 19 / 384)
    rw [hinv] at hlog
    have hL2 : Real.log ξ⁻¹ ^ 2 ≤ (ξ ^ (-(19 / 384 : ℝ)) / (19 / 384)) ^ 2 :=
      pow_le_pow_left₀ hL0 hlog 2
    have he : 0 ≤ ξ ^ (19 / 96 : ℝ) := Real.rpow_nonneg hξ.le _
    calc ξ ^ (19 / 96 : ℝ) * Real.log ξ⁻¹ ^ 2
        ≤ ξ ^ (19 / 96 : ℝ) * (ξ ^ (-(19 / 384 : ℝ)) / (19 / 384)) ^ 2 :=
          mul_le_mul_of_nonneg_left hL2 he
      _ = (384 / 19) ^ 2 * (ξ ^ (19 / 96 : ℝ) * (ξ ^ (-(19 / 384 : ℝ))) ^ 2) := by ring
      _ = (384 / 19) ^ 2 * ξ ^ (19 / 192 : ℝ) := by
          have e2 : (ξ ^ (-(19 / 384 : ℝ))) ^ 2 = ξ ^ (-(19 / 192 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hξ.le]
            norm_num
          rw [e2, ← Real.rpow_add hξ]
          norm_num

/-- `Kδ ≤ 2 ξ^{99/200}` when `K ξ^{103/600} ≤ 2` (`2/3 − 99/200 = 103/600`). -/
theorem Tight.mul_dlt_le_of_mul_rpow_le {ξ K : ℝ} (hξ : 0 < ξ) (hK : K * ξ ^ (103 / 600 : ℝ) ≤ 2) :
    K * ξ ^ (2 / 3 : ℝ) ≤ 2 * ξ ^ (99 / 200 : ℝ) := by
  have e : ξ ^ (2 / 3 : ℝ) = ξ ^ (103 / 600 : ℝ) * ξ ^ (99 / 200 : ℝ) := by
    rw [← Real.rpow_add hξ]
    norm_num
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hξ.le _)

/-! ## Lemma `lem:band-event-K` from Lemma 5.1 and the mean bound -/

/-- **Lemma `lem:band-event-K`, reduced to Lemma 5.1 and Proposition `prop:mean`.** The hypotheses `h51` and
`hmean` are, verbatim, the planned conclusions of `lemma51` and `mean_maxDev_le` (BP2 §5 block); the
conclusion is, verbatim, the planned conclusion of `bandEv_scale_le` (BP2 §6 block). The constant is
`C = C₅⁺ (1 + C₆⁺)`.

Proof. Fix `η`, `K ≥ 1`, `ε > 0`. For small `γ` (`γ ≤ γ₅, γ₆`, `ξ ≤ γ < 1`, `K γ^{103/600} < 2` and the remainder
bounds below), `R = Kδ` satisfies `δ ≤ R ≤ 2ξ^{99/200}`, and `m = E M(η γ) ≤ C₆⁺ δ` (the Bochner integral is the
real part of the finite lower integral). Lemma 5.1 and `Tight.lemma51_rhs_le` give
`P[𝒢 ∩ ℬ(Kδ)] ≤ C₅⁺ (K^{-3} + C₆⁺ K^{-4} + ξ^{97/300} L + ξ^{19/96} L²)`, and
`C₅⁺ (ξ^{97/300} L + ξ^{19/96} L²) ≤ C₅⁺ ((600/97) γ^{97/600} + (384/19)² γ^{19/192}) < ε`. -/
theorem bandEv_scale_le_of_lemma51 (G : GSetup)
    (h51 : ∃ C γ₁, 0 < γ₁ ∧ ∀ γ ∈ Ioc (0:ℝ) γ₁, ∀ η : Coord → C(unitInterval, ℂ), Measurable η →
      (∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η ω)) →
      ∀ R, dlt γ ≤ R → R ≤ 2 * xiGamma γ ^ (99/200 : ℝ) →
        stdP {ω | goodEv G γ ω ∧ bandEv γ R (η ω)} ≤ ENNReal.ofReal (C * (xiGamma γ ^ 2 / R ^ 3 +
          xiGamma γ ^ 2 * ((∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99/100:ℝ) * Lg γ) / R ^ 4 +
          xiGamma γ ^ (49/32 : ℝ) * Lg γ ^ 2 / R ^ 2)))
    (hmean : ∃ C γ₁, 0 < γ₁ ∧ ∀ γ ∈ Ioc (0:ℝ) γ₁, ∀ η : Coord → C(unitInterval, ℂ), Measurable η →
      (∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η ω)) →
      ∫⁻ ω, ENNReal.ofReal (maxDev (η ω)) ∂stdP ≤ ENNReal.ofReal (C * dlt γ)) :
    ∃ C, ∀ η : ℝ → Coord → C(unitInterval, ℂ), (∀ γ, Measurable (η γ)) →
      (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)) →
      ∀ K, 1 ≤ K → ∀ ε, 0 < ε → ∀ᶠ γ in 𝓝[>] (0:ℝ),
        stdP {ω | goodEv G γ ω ∧ bandEv γ (K * dlt γ) (η γ ω)} ≤
          ENNReal.ofReal (C * (K ^ (-3:ℝ) + K ^ (-4:ℝ)) + ε) := by
  obtain ⟨C₅, γ₅, hγ₅, h5⟩ := h51
  obtain ⟨C₆, γ₆, hγ₆, h6⟩ := hmean
  obtain ⟨γ₀, hγ₀, hγ₀1, hξ⟩ := exists_xiGamma_pos_le
  set A : ℝ := max C₅ 0 with hA
  set B : ℝ := max C₆ 0 with hB
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  refine ⟨A * (1 + B), fun η hm hη K hK ε hε => ?_⟩
  have hK0 : 0 < K := by linarith
  have hγ₁0 : 0 < min (min γ₅ γ₆) γ₀ := lt_min (lt_min hγ₅ hγ₆) hγ₀
  filter_upwards [Tight.eventually_mem_Ioo_zero hγ₁0,
    Tight.eventually_mul_rpow_lt K (q := 103 / 600) (by norm_num) (by norm_num : (0 : ℝ) < 2),
    Tight.eventually_mul_rpow_lt (A * (600 / 97)) (q := 97 / 600) (by norm_num)
      (by positivity : (0 : ℝ) < ε / 2),
    Tight.eventually_mul_rpow_lt (A * (384 / 19) ^ 2) (q := 19 / 192) (by norm_num)
      (by positivity : (0 : ℝ) < ε / 2)] with γ hγ hKγ hv1 hv2
  have hγ0 : 0 < γ := hγ.1
  have hγ₅' : γ ≤ γ₅ := hγ.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγ₆' : γ ≤ γ₆ := hγ.2.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγ₀' : γ ≤ γ₀ := hγ.2.le.trans (min_le_right _ _)
  have hγ2 : γ < 2 := by linarith
  obtain ⟨hξ0, hξγ⟩ := hξ γ ⟨hγ0, hγ₀'⟩
  have hξ1 : xiGamma γ ≤ 1 := by linarith
  set ξ := xiGamma γ with hξdef
  -- the scale `R = Kδ` is admissible
  have hR1 : dlt γ ≤ K * dlt γ := le_mul_of_one_le_left (Real.rpow_nonneg hξ0.le _) hK
  have hR2 : K * dlt γ ≤ 2 * ξ ^ (99 / 200 : ℝ) := by
    refine Tight.mul_dlt_le_of_mul_rpow_le hξ0 ?_
    calc K * ξ ^ (103 / 600 : ℝ) ≤ K * γ ^ (103 / 600 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hξ0.le hξγ (by norm_num)) hK0.le
      _ ≤ 2 := hKγ.le
  have h5γ := h5 γ ⟨hγ0, hγ₅'⟩ (η γ) (hm γ) (hη γ hγ0 hγ2) (K * dlt γ) hR1 hR2
  -- the mean `m = E M(η γ)`
  set m : ℝ := ∫ ω, maxDev (η γ ω) ∂stdP with hm_def
  have hm0 : 0 ≤ m := integral_nonneg fun ω => maxDev_nonneg _
  have hmle : m ≤ B * ξ ^ (2 / 3 : ℝ) := by
    have hl := h6 γ ⟨hγ0, hγ₆'⟩ (η γ) (hm γ) (hη γ hγ0 hγ2)
    have hmeas : AEStronglyMeasurable (fun ω => maxDev (η γ ω)) stdP :=
      (measurable_maxDev_comp (hm γ)).aestronglyMeasurable
    rw [hm_def, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => maxDev_nonneg _) hmeas]
    calc (∫⁻ ω, ENNReal.ofReal (maxDev (η γ ω)) ∂stdP).toReal
        ≤ (ENNReal.ofReal (C₆ * dlt γ)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
      _ = max (C₆ * dlt γ) 0 := ENNReal.toReal_ofReal'
      _ ≤ B * ξ ^ (2 / 3 : ℝ) := by
          refine max_le ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hξ0.le _)
  -- the right side of Lemma 5.1 at `R = Kδ`
  set L : ℝ := Lg γ with hL_def
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ hξ0).2 hξ1)
  set T : ℝ := ξ ^ 2 / (K * dlt γ) ^ 3 +
      ξ ^ 2 * (m + ξ ^ (99 / 100 : ℝ) * L) / (K * dlt γ) ^ 4 +
      ξ ^ (49 / 32 : ℝ) * L ^ 2 / (K * dlt γ) ^ 2 with hT
  have hT0 : 0 ≤ T := by
    have hd0 : 0 < K * dlt γ := mul_pos hK0 (Real.rpow_pos_of_pos hξ0 _)
    have : 0 ≤ ξ ^ (99 / 100 : ℝ) * L := mul_nonneg (Real.rpow_nonneg hξ0.le _) hL0
    have : 0 ≤ ξ ^ (49 / 32 : ℝ) * L ^ 2 := mul_nonneg (Real.rpow_nonneg hξ0.le _) (sq_nonneg _)
    positivity
  have hTle : T ≤ K ^ (-3 : ℝ) + B * K ^ (-4 : ℝ) +
      (ξ ^ (97 / 300 : ℝ) * L + ξ ^ (19 / 96 : ℝ) * L ^ 2) :=
    Tight.lemma51_rhs_le hξ0 hK hmle hL0
  -- the remainder is at most `ε / A`-small
  obtain ⟨hr1, hr2⟩ := Tight.rpow_mul_log_inv_le hξ0 hξ1
  have hV : A * (ξ ^ (97 / 300 : ℝ) * L + ξ ^ (19 / 96 : ℝ) * L ^ 2) ≤ ε := by
    have g1 : ξ ^ (97 / 600 : ℝ) ≤ γ ^ (97 / 600 : ℝ) := Real.rpow_le_rpow hξ0.le hξγ (by norm_num)
    have g2 : ξ ^ (19 / 192 : ℝ) ≤ γ ^ (19 / 192 : ℝ) := Real.rpow_le_rpow hξ0.le hξγ (by norm_num)
    have k1 : A * (ξ ^ (97 / 300 : ℝ) * L) ≤ A * (600 / 97) * γ ^ (97 / 600 : ℝ) := by
      calc A * (ξ ^ (97 / 300 : ℝ) * L) ≤ A * (600 / 97 * ξ ^ (97 / 600 : ℝ)) :=
            mul_le_mul_of_nonneg_left hr1 hA0
        _ ≤ A * (600 / 97 * γ ^ (97 / 600 : ℝ)) := by gcongr
        _ = A * (600 / 97) * γ ^ (97 / 600 : ℝ) := by ring
    have k2 : A * (ξ ^ (19 / 96 : ℝ) * L ^ 2) ≤ A * (384 / 19) ^ 2 * γ ^ (19 / 192 : ℝ) := by
      calc A * (ξ ^ (19 / 96 : ℝ) * L ^ 2) ≤ A * ((384 / 19) ^ 2 * ξ ^ (19 / 192 : ℝ)) :=
            mul_le_mul_of_nonneg_left hr2 hA0
        _ ≤ A * ((384 / 19) ^ 2 * γ ^ (19 / 192 : ℝ)) := by gcongr
        _ = A * (384 / 19) ^ 2 * γ ^ (19 / 192 : ℝ) := by ring
    linarith
  -- assemble
  have hKpos3 : 0 ≤ K ^ (-3 : ℝ) := Real.rpow_nonneg hK0.le _
  have hKpos4 : 0 ≤ K ^ (-4 : ℝ) := Real.rpow_nonneg hK0.le _
  refine h5γ.trans (ENNReal.ofReal_le_ofReal ?_)
  calc C₅ * T ≤ A * T := mul_le_mul_of_nonneg_right (le_max_left _ _) hT0
    _ ≤ A * (K ^ (-3 : ℝ) + B * K ^ (-4 : ℝ) +
          (ξ ^ (97 / 300 : ℝ) * L + ξ ^ (19 / 96 : ℝ) * L ^ 2)) := mul_le_mul_of_nonneg_left hTle hA0
    _ = A * (K ^ (-3 : ℝ) + B * K ^ (-4 : ℝ)) +
          A * (ξ ^ (97 / 300 : ℝ) * L + ξ ^ (19 / 96 : ℝ) * L ^ 2) := by ring
    _ ≤ A * (1 + B) * (K ^ (-3 : ℝ) + K ^ (-4 : ℝ)) + ε := by
        have : A * (K ^ (-3 : ℝ) + B * K ^ (-4 : ℝ)) ≤ A * (1 + B) * (K ^ (-3 : ℝ) + K ^ (-4 : ℝ)) := by
          have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
          nlinarith [mul_nonneg hA0 hKpos3, mul_nonneg hA0 hKpos4, mul_nonneg hAB hKpos3]
        linarith

end SmallGammaGeodesics
