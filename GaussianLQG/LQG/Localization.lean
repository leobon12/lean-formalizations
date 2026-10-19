import GaussianLQG.LQG.Localization.Moments

/-!
# Localization and ball masses (blueprint Lemma `lem:T-B`)

Fix a compact `K ⊂ ℂ` and `δ > 0`, and let `T`, `B`, `Θ` be the `[0, ∞]`-valued random variables
`Setup.locT`, `Setup.locB`, `Setup.locTheta` of blueprint Lemma `lem:T-B` (definitions in
`GaussianLQG.LQG.Localization.Defs`). This file states the lemma:

* `Setup.measurable_loc`: `T`, `B`, `Θ` are measurable;
* the pathwise statements (`Setup.range_subset_ball_locT`, `Setup.lengthMeasure_ball_le_locB`,
  `Setup.isRegular_and_energy_le_locTheta` in `…Localization.Deterministic`) hold for every `ω` with
  `T(ω) < ∞` (and `B(ω) < ∞` for the energy bound);
* `Setup.exists_locMoments`: for every `p ≥ 1` there is `γ_* = γ_*(p) > 0` such that, for every
  compact `K` and `δ > 0`, `P[T < ∞] = 1` and `sup_{γ ≤ γ_*} E[T^p + B^p + Θ^p] ≤ C_{p,K,δ} < ∞`;
* `Setup.ae_localization`: for `γ ≤ γ_*(1)`, almost surely `T, B, Θ < ∞` and every constant-speed
  `D^γ`-geodesic `η` between points `z, w ∈ K` with `|z - w| ≥ δ` satisfies
  `η([0,1]) ⊆ B_T(0)`, `ν_η(B_r(u)) ≤ B r^{1/2}` (`u ∈ ℂ`, `r ∈ (0, 1]`), and `ν_η` is regular
  with `ℰ(ν_η, ν_η) ≤ Θ²` (blueprint (`eq:T-B`)).

The theorems take Lemma `lem:scaling`(c),(d) (`Setup.HolderScaling`, `Setup.AnnulusScaling`) as
hypotheses: these interface lemmas are proved separately for every `Setup`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

namespace Setup

/-- **Blueprint Lemma `lem:T-B`, measurability.** `T`, `B` and `Θ` are random variables. -/
theorem measurable_loc (S : Setup) (γ : ℝ) (K : Set ℂ) (δ : ℝ) :
    Measurable (S.locT γ K) ∧ Measurable (S.locB γ K δ) ∧ Measurable (S.locTheta γ K δ) :=
  ⟨S.measurable_locT γ K, S.measurable_locB γ K δ, S.measurable_locTheta γ K δ⟩

/-- **Blueprint Lemma `lem:T-B`, moments.** Assume Lemma `lem:scaling`(c),(d). For every
`p ∈ [1, ∞)` there is `γ_* > 0` (depending only on `p`) such that for every compact `K` and every
`δ > 0` there is `C = C_{p,K,δ} < ∞` with, for all `γ ∈ (0, γ_*]`: `P[T < ∞] = 1` and
`E[T^p + B^p + Θ^p] ≤ C`. -/
theorem exists_locMoments (S : Setup) (hA : S.HolderScaling) (hL : S.AnnulusScaling) :
    ∀ p : ℝ, 1 ≤ p → ∃ γs : ℝ, 0 < γs ∧ ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ γ ∈ Ioc (0 : ℝ) γs,
        (∀ᵐ ω ∂stdP, S.locT γ K ω ≠ ⊤) ∧
        ∫⁻ ω, (S.locT γ K ω ^ p + S.locB γ K δ ω ^ p + S.locTheta γ K δ ω ^ p) ∂stdP ≤ C := by
  intro p hp
  set N : ℝ := 4 * p + 4 with hN
  have hNpos : 0 < N := by linarith
  set ε : ℝ := 1 / (4 * N) with hε
  have hεpos : 0 < ε := by positivity
  have h4Nε : 4 * N * ε = 1 := by rw [hε]; field_simp
  obtain ⟨γε, hγε, -, hexp⟩ := S.exists_exponent_bounds hεpos
  obtain ⟨γL, CL, hγL, hLs⟩ := hL (4 * N) (by linarith)
  obtain ⟨γA, CA, hγA, hAs⟩ := hA (4 * p) (by linarith)
  obtain ⟨γ6, hγ6, h6⟩ := S.S6 (4 * N) (by linarith)
  obtain ⟨γ6', hγ6', h6'⟩ := S.S6 (2 * p) (by linarith)
  refine ⟨min (min γε γL) (min γA (min γ6 γ6')),
    lt_min (lt_min hγε hγL) (lt_min hγA (lt_min hγ6 hγ6')), ?_⟩
  intro K hK δ hδ
  obtain ⟨C6, hC6, h6K⟩ := h6 K hK δ hδ
  obtain ⟨C6', hC6', h6K'⟩ := h6' K hK δ hδ
  have hKb : Bornology.IsBounded K := hK.isBounded
  set CL' : ℝ := max CL 0 with hCL'
  set CA' : ℝ := max CA 0 with hCA'
  set eA : ℝ := 2 * p + 2 with heA
  -- the constants
  set Ctail : ℝ≥0∞ := ENNReal.ofReal (Metric.diam K ^ (1 / 2 : ℝ)) ^ (4 * N) * C6 +
    ENNReal.ofReal CL' with hCtail_def
  have hCtail : Ctail ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith)
      ENNReal.ofReal_ne_top) hC6, ENNReal.ofReal_ne_top⟩
  set CT : ℝ≥0∞ := ENNReal.ofReal (2 * (2 ^ 0 * locR0 K)) ^ p +
    ∑' j : ℕ, ENNReal.ofReal (2 * (2 ^ (j + 1) * locR0 K)) ^ p *
      (Ctail * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) with hCT_def
  have hCT : CT ≠ ⊤ := locT_bound_ne_top K (by linarith) (by linarith) hCtail
  set CA2 : ℝ≥0∞ := ENNReal.ofReal (CA' * (2 * (2 ^ 0 * locR0 K)) ^ eA) ^ (1 / 2 : ℝ) +
    ∑' j : ℕ, ENNReal.ofReal (CA' * (2 * (2 ^ (j + 1) * locR0 K)) ^ eA) ^ (1 / 2 : ℝ) *
      (Ctail * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) ^ (1 / 2 : ℝ) with hCA2_def
  have hCA2 : CA2 ≠ ⊤ := holder_bound_ne_top K (le_max_right _ _) (by linarith) hCtail
  set CB : ℝ≥0∞ := 1 + ENNReal.ofReal (Real.sqrt 2) ^ p * (CA2 ^ (1 / 2 : ℝ) * C6' ^ (1 / 2 : ℝ))
    with hCB_def
  have hCB : CB ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCA2)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC6'))⟩
  set CΘ : ℝ≥0∞ := 2 ^ p * (CB + CT) with hCΘ_def
  have hCΘ : CΘ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.add_ne_top.2 ⟨hCB, hCT⟩)
  refine ⟨CT + CB + CΘ, ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hCT, hCB⟩, hCΘ⟩, ?_⟩
  rintro γ ⟨hγ0, hγ⟩
  have hγε' : γ ≤ γε := hγ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγL' : γ ≤ γL := hγ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγA' : γ ≤ γA := hγ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγ6a : γ ≤ γ6 :=
    hγ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hγ6b : γ ≤ γ6' :=
    hγ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hξ, hξε, hξQ⟩ := hexp γ ⟨hγ0, hγε'⟩
  -- the exponents: `ξQ ∈ [1 - ε, 1 + ε]` and `4Nξ ≤ 1`
  have hQlo : 1 - ε ≤ S.ξ γ * Q γ := by
    have := neg_abs_le (S.ξ γ * Q γ - 1)
    linarith
  have hQhi : S.ξ γ * Q γ ≤ 1 + ε := by
    have := le_abs_self (S.ξ γ * Q γ - 1)
    linarith
  have h4Nξ : 4 * N * S.ξ γ ≤ 1 := by
    calc 4 * N * S.ξ γ ≤ 4 * N * ε := mul_le_mul_of_nonneg_left hξε (by positivity)
      _ = 1 := h4Nε
  have hexpL : -(4 * N * (S.ξ γ * Q γ)) + (4 * N) ^ 2 * S.ξ γ ^ 2 ≤ -(2 * N) := by
    have h1 : (4 * N) ^ 2 * S.ξ γ ^ 2 ≤ 1 := by
      rw [← mul_pow]
      exact pow_le_one₀ (by positivity) h4Nξ
    have h2 : 4 * N * (1 - ε) ≤ 4 * N * (S.ξ γ * Q γ) :=
      mul_le_mul_of_nonneg_left hQlo (by positivity)
    have h3 : 4 * N * (1 - ε) = 4 * N - 1 := by rw [mul_sub, mul_one, h4Nε]
    linarith
  have h4pξ : 4 * p * S.ξ γ ≤ 1 := by
    calc 4 * p * S.ξ γ ≤ 4 * N * S.ξ γ := mul_le_mul_of_nonneg_right (by linarith) hξ.le
      _ ≤ 1 := h4Nξ
  have h4pε : 4 * p * ε ≤ 1 := by
    calc 4 * p * ε ≤ 4 * N * ε := mul_le_mul_of_nonneg_right (by linarith) hεpos.le
      _ = 1 := h4Nε
  have hexpA : 4 * p * (S.ξ γ * Q γ - 1 / 2) + (4 * p) ^ 2 * S.ξ γ ^ 2 ≤ eA := by
    have h1 : (4 * p) ^ 2 * S.ξ γ ^ 2 ≤ 1 := by
      rw [← mul_pow]
      exact pow_le_one₀ (by positivity) h4pξ
    have h2 : 4 * p * (S.ξ γ * Q γ - 1 / 2) ≤ 4 * p * (1 / 2 + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : 4 * p * (1 / 2 + ε) = 2 * p + 4 * p * ε := by ring
    linarith
  -- Lemma `lem:scaling`(d) at order `4N`: `E[L_R^{-4N}] ≤ C R^{-2N}`
  have hLm : ∀ R : ℝ, 1 ≤ R → ∫⁻ ω, (annulusCross (S.D γ ω).1 R)⁻¹ ^ (4 * N) ∂stdP ≤
      ENNReal.ofReal (CL' * R ^ (-(2 * N))) :=
    fun R hR => (hLs γ ⟨hγ0, hγL'⟩ R hR).trans (ofReal_mul_rpow_le_max hR hexpL)
  -- Lemma `lem:scaling`(c) at order `4p`: `E[A_γ(B̄_R)^{4p}] ≤ C R^{2p+2}`
  have hAm : ∀ R : ℝ, 1 ≤ R →
      ∫⁻ ω, holderConst (S.D γ ω).1 (Metric.closedBall 0 R) ^ (2 * (2 * p)) ∂stdP ≤
        ENNReal.ofReal (CA' * R ^ eA) := by
    intro R hR
    rw [show 2 * (2 * p) = 4 * p by ring]
    exact (hAs γ ⟨hγ0, hγA'⟩ R hR).trans (ofReal_mul_rpow_le_max hR hexpA)
  -- the tail bound `P[L_{2^j R₀} ≤ U] ≤ C (2^j R₀)^{-N}`
  have htail : ∀ j : ℕ, stdP {ω | annulusCross (S.D γ ω).1 (2 ^ j * locR0 K) ≤ S.locU γ K ω} ≤
      Ctail * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N)) := by
    intro j
    have hR1 : 1 ≤ 2 ^ j * locR0 K :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (one_le_locR0 K)
    exact measure_annulusCross_le_locU hKb hNpos (by linarith) (h6K γ ⟨hγ0, hγ6a⟩).1
      (le_max_right _ _) (hLm _ hR1)
  -- `E[T^p] ≤ C`, hence `T < ∞` a.s.
  have hTm : ∫⁻ ω, S.locT γ K ω ^ p ∂stdP ≤ CT := lintegral_locT_rpow_le (by linarith) htail
  have hTfin : ∀ᵐ ω ∂stdP, S.locT γ K ω ≠ ⊤ := by
    filter_upwards [ae_lt_top ((S.measurable_locT γ K).pow_const p)
      (ne_top_of_le_ne_top hCT hTm)] with ω hω htop
    rw [htop, ENNReal.top_rpow_of_pos (by linarith)] at hω
    exact lt_irrefl _ hω
  -- `E[A_γ(B̄_T)^{2p}] ≤ C`
  have hA2 : ∫⁻ ω, holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) ^ (2 * p)
      ∂stdP ≤ CA2 :=
    lintegral_holderConst_locT_le hTfin htail hAm
  -- `E[B^p] ≤ C` and `E[Θ^p] ≤ C`
  have hBm : ∫⁻ ω, S.locB γ K δ ω ^ p ∂stdP ≤ CB := by
    refine (lintegral_locB_rpow_le (by linarith)).trans ?_
    rw [hCB_def]
    exact add_le_add le_rfl (mul_le_mul_right (mul_le_mul' (ENNReal.rpow_le_rpow hA2 (by norm_num))
      (ENNReal.rpow_le_rpow (h6K' γ ⟨hγ0, hγ6b⟩).2 (by norm_num))) _)
  have hΘm : ∫⁻ ω, S.locTheta γ K δ ω ^ p ∂stdP ≤ CΘ :=
    (lintegral_locTheta_rpow_le (by linarith)).trans
      (by rw [hCΘ_def]; exact mul_le_mul_right (add_le_add hBm hTm) _)
  refine ⟨hTfin, ?_⟩
  have hTp := (S.measurable_locT γ K).pow_const p
  have hBp := (S.measurable_locB γ K δ).pow_const p
  have hTB : Measurable fun ω => S.locT γ K ω ^ p + S.locB γ K δ ω ^ p := hTp.add hBp
  rw [lintegral_add_left hTB, lintegral_add_left hTp]
  exact add_le_add (add_le_add hTm hBm) hΘm

/-- **Blueprint Lemma `lem:T-B`, almost-sure statements (`eq:T-B`).** Assume Lemma
`lem:scaling`(c),(d). There is `γ_T > 0` such that for `γ ∈ (0, γ_T]`, every compact `K` and every
`δ > 0`, almost surely `T, B, Θ < ∞` and every constant-speed `D^γ`-geodesic `η` from `z ∈ K` to
`w ∈ K` with `|z - w| ≥ δ` satisfies `η([0,1]) ⊆ B_T(0)`, `ν_η(B_r(u)) ≤ B r^{1/2}` for `u ∈ ℂ`,
`r ∈ (0, 1]`, and `ν_η` is regular with `ℰ(ν_η, ν_η) ≤ Θ²`. -/
theorem ae_localization (S : Setup) (hA : S.HolderScaling) (hL : S.AnnulusScaling) :
    ∃ γT : ℝ, 0 < γT ∧ ∀ γ ∈ Ioc (0 : ℝ) γT, ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
      ∀ᵐ ω ∂stdP, S.locT γ K ω ≠ ⊤ ∧ S.locB γ K δ ω ≠ ⊤ ∧ S.locTheta γ K δ ω ≠ ⊤ ∧
        ∀ z ∈ K, ∀ w ∈ K, δ ≤ ‖z - w‖ → ∀ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η →
          range η ⊆ Metric.ball 0 (S.locT γ K ω).toReal ∧
          (∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 →
            (lengthMeasure η (Metric.ball u r)).toReal ≤
              (S.locB γ K δ ω).toReal * r ^ (1 / 2 : ℝ)) ∧
          IsRegular (lengthMeasure η) ∧
          energy (lengthMeasure η) (lengthMeasure η) ≤ (S.locTheta γ K δ ω).toReal ^ 2 := by
  obtain ⟨γs, hγs, hmom⟩ := S.exists_locMoments hA hL 1 le_rfl
  refine ⟨γs, hγs, fun γ hγ K hK δ hδ => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hmom K hK δ hδ
  obtain ⟨hTfin, hint⟩ := hbound γ hγ
  have hmeas : Measurable fun ω =>
      S.locT γ K ω ^ (1 : ℝ) + S.locB γ K δ ω ^ (1 : ℝ) + S.locTheta γ K δ ω ^ (1 : ℝ) :=
    (((S.measurable_locT γ K).pow_const _).add ((S.measurable_locB γ K δ).pow_const _)).add
      ((S.measurable_locTheta γ K δ).pow_const _)
  have hKb : Bornology.IsBounded K := hK.isBounded
  filter_upwards [hTfin, ae_lt_top hmeas (ne_top_of_le_ne_top hC hint)] with ω hT hsum
  simp only [ENNReal.rpow_one] at hsum
  have hB : S.locB γ K δ ω ≠ ⊤ := fun h => by
    rw [h, add_top, top_add] at hsum
    exact lt_irrefl _ hsum
  have hΘ : S.locTheta γ K δ ω ≠ ⊤ := fun h => by
    rw [h, add_top] at hsum
    exact lt_irrefl _ hsum
  refine ⟨hT, hB, hΘ, fun z hz w hw hzw η hη => ⟨range_subset_ball_locT hKb hT hz hw hη,
    fun u r hr _ => ?_, isRegular_and_energy_le_locTheta hKb hδ hT hB hz hw hzw hη⟩⟩
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hB]
  exact lengthMeasure_ball_le_locB hKb hδ hT hz hw hzw hη u hr

end Setup

end GaussianLQG
