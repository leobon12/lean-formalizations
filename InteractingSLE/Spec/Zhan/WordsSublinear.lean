/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal
import BrownianMotion.StochasticIntegral.DoobLp
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Brownian sublinearity

Packet PROVE-ZHAN-B4. The linear escape of strip gaps (Astra (3.24), "Brownian sublinearity gives `√κ|B_s| ≤ εs`
eventually", `source/external/AstraIG1/ig1_formalization_proofs.txt` L1553–L1556) needs: almost surely, for every
`ε > 0` there is `C` with `|B_u| ≤ C + ε u` for all `u ≥ 0`.

Proof: a filtered Brownian motion is a martingale at rational times (independent centred increments); Doob's weak
maximal inequality for the countable index `ℚ≥0` (vendored `ProbabilityTheory.maximal_ineq_norm_countable`) gives
`P(sup_{q ≤ 2^k} |B_q| ≥ ε 2^k) ≤ E|B_{2^k}| / (ε 2^k) ≤ ε⁻¹ 2^{−k/2}` (`E|B_t| ≤ √t` from `E B_t² = t`), which is
summable; Borel–Cantelli and continuity of the paths conclude.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

/-- The filtration at rational times. -/
def ratFiltration (𝓕 : Filtration ℝ≥0 mΩ) : Filtration ℚ≥0 mΩ where
  seq q := 𝓕 (q : ℝ≥0)
  mono' p q hpq := 𝓕.mono (by exact_mod_cast hpq)
  le' q := 𝓕.le _

/-- **A filtered Brownian motion is a martingale at rational times.** -/
theorem martingale_ratFiltration [IsProbabilityMeasure P] (hB : IsFilteredBrownianReal 𝓕 B P) :
    Martingale (fun q : ℚ≥0 => B q) (ratFiltration 𝓕) P := by
  have hpre := hB.1.toIsPreBrownianReal
  refine ⟨fun q => (hB.2.1 q).stronglyMeasurable, fun i j hij => ?_⟩
  have hij' : (i : ℝ≥0) ≤ j := by exact_mod_cast hij
  have hint : ∀ t, Integrable (B t) P := hpre.integrable_eval
  have hmeas : StronglyMeasurable[MeasurableSpace.comap (B j - B i) inferInstance] (B j - B i) :=
    (Measurable.of_comap_le le_rfl).stronglyMeasurable
  have hle₁ : MeasurableSpace.comap (B j - B i) inferInstance ≤ mΩ :=
    (((hB.2.1 j).mono (𝓕.le _) le_rfl).sub ((hB.2.1 i).mono (𝓕.le _) le_rfl)).comap_le
  have hind : Indep (MeasurableSpace.comap (B j - B i) inferInstance) (𝓕 (i : ℝ≥0)) P := by
    have := hB.2.2 i j hij'
    exact this
  have h1 := condExp_indep_eq hle₁ (𝓕.le (i : ℝ≥0)) hmeas hind
  have h0 : P[B j - B i] = 0 := by
    simp only [Pi.sub_apply]
    rw [integral_sub (hint j) (hint i), hpre.integral_eval, hpre.integral_eval, sub_zero]
  have h2 : P[B i | 𝓕 (i : ℝ≥0)] = B i :=
    condExp_of_stronglyMeasurable (𝓕.le _) (hB.2.1 i).stronglyMeasurable (hint i)
  show P[B j | 𝓕 (i : ℝ≥0)] =ᵐ[P] B i
  have hsplit : B j = (B j - B i) + B i := by funext ω; simp
  rw [hsplit]
  filter_upwards [condExp_add ((hint j).sub (hint i)) (hint i) (𝓕 (i : ℝ≥0)), h1] with ω hω h1ω
  rw [hω, Pi.add_apply, h1ω, h0, h2, zero_add]

/-- `E|B_t| ≤ √t`. -/
theorem integral_abs_le_sqrt [IsProbabilityMeasure P] (hB : IsPreBrownianReal B P) {t : ℝ≥0} (ht : 0 < t) :
    ∫ ω, |B t ω| ∂P ≤ Real.sqrt t := by
  have hlaw := hB.hasLaw_eval t
  have hsq : ∫ ω, B t ω ^ 2 ∂P = t := by
    have h := hB.covariance_eval t t
    rw [covariance_self (hB.aemeasurable t), variance_of_integral_eq_zero (hB.aemeasurable t)
      (hB.integral_eval t), min_self] at h
    simpa using h
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 (by exact_mod_cast ht)
  have hint2 : Integrable (fun ω => B t ω ^ 2) P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable_sq
  have hbound : ∀ ω, |B t ω| ≤ (B t ω ^ 2 + t) / (2 * Real.sqrt t) := fun ω => by
    rw [le_div_iff₀ (by positivity)]
    have h1 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (|B t ω| - Real.sqrt t), sq_abs (B t ω)]
  calc ∫ ω, |B t ω| ∂P ≤ ∫ ω, (B t ω ^ 2 + t) / (2 * Real.sqrt t) ∂P :=
        integral_mono ((hB.integrable_eval t).abs) ((hint2.add (integrable_const _)).div_const _) hbound
    _ = Real.sqrt t := by
        rw [integral_div, integral_add hint2 (integrable_const _), hsq, integral_const, probReal_univ,
          one_smul, ← two_mul]
        have h1 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by positivity)
        field_simp
        nlinarith [h1]

local instance : Countable ℚ≥0 := inferInstanceAs (Countable {q : ℚ // 0 ≤ q})

/-- The dyadic block event: the running maximum over rational times `≤ 2^k` reaches `ε 2^k`. -/
def blockEvent (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (k : ℕ) : Set Ω :=
  {ω | ε * 2 ^ k ≤ ⨆ i : Set.Iic ((2 : ℚ≥0) ^ k), ‖B (i : ℚ≥0) ω‖}

/-- **Doob's weak inequality on a dyadic block**: `P(blockEvent ε k) ≤ √(2^k)/(ε 2^k)`. -/
theorem measureReal_blockEvent_le [IsProbabilityMeasure P] (hB : IsFilteredBrownianReal 𝓕 B P) {ε : ℝ}
    (hε : 0 < ε) (k : ℕ) : P.real (blockEvent B ε k) ≤ Real.sqrt (2 ^ k) / (ε * 2 ^ k) := by
  have hmar := martingale_ratFiltration hB
  have hpos : 0 < ε * 2 ^ k := by positivity
  set ε' : ℝ≥0 := ⟨ε * 2 ^ k, hpos.le⟩
  have h := maximal_ineq_norm_countable hmar ε' ((2 : ℚ≥0) ^ k)
  have hcast : (((2 : ℚ≥0) ^ k : ℚ≥0) : ℝ≥0) = (2 : ℝ≥0) ^ k := by push_cast; rfl
  have hcastR : ((((2 : ℚ≥0) ^ k : ℚ≥0) : ℝ≥0) : ℝ) = 2 ^ k := by rw [hcast]; push_cast; rfl
  have hE : ∫ ω, ‖B ((2 : ℚ≥0) ^ k : ℚ≥0) ω‖ ∂P ≤ Real.sqrt (2 ^ k) := by
    simp only [Real.norm_eq_abs]
    have := integral_abs_le_sqrt hB.1.toIsPreBrownianReal (t := (((2 : ℚ≥0) ^ k : ℚ≥0) : ℝ≥0))
      (by rw [hcast]; positivity)
    rwa [hcastR] at this
  have hset : ∫ ω in {ω | (ε' : ℝ) ≤ ⨆ i : Set.Iic ((2 : ℚ≥0) ^ k), ‖B (i : ℚ≥0) ω‖},
      ‖B ((2 : ℚ≥0) ^ k : ℚ≥0) ω‖ ∂P ≤ ∫ ω, ‖B ((2 : ℚ≥0) ^ k : ℚ≥0) ω‖ ∂P :=
    setIntegral_le_integral ((hB.1.toIsPreBrownianReal.integrable_eval _).norm)
      (Eventually.of_forall fun _ => norm_nonneg _)
  have h2 : ε' • P.real (blockEvent B ε k) ≤ Real.sqrt (2 ^ k) := (h.trans hset).trans hE
  rw [NNReal.smul_def, smul_eq_mul] at h2
  rw [le_div_iff₀ hpos, mul_comm]
  exact h2

/-- **Borel–Cantelli on dyadic blocks**: almost surely the block events eventually fail. -/
theorem ae_eventually_not_blockEvent [IsProbabilityMeasure P] (hB : IsFilteredBrownianReal 𝓕 B P) {ε : ℝ}
    (hε : 0 < ε) : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ blockEvent B ε k := by
  have hb : ∀ k : ℕ, P (blockEvent B ε k) ≤ ENNReal.ofReal (ε⁻¹ * (Real.sqrt 2)⁻¹ ^ k) := fun k => by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((measureReal_blockEvent_le hB hε k).trans (le_of_eq ?_))
    have h2 : Real.sqrt (2 ^ k) = Real.sqrt 2 ^ k := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
        Real.mul_self_sqrt (by norm_num)]
    have hs : Real.sqrt 2 ^ k ≠ 0 := pow_ne_zero _ (by positivity)
    rw [h2, inv_pow, show (2 : ℝ) ^ k = Real.sqrt 2 ^ k * Real.sqrt 2 ^ k by
      rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]]
    field_simp
  have hsum : ∑' k, P (blockEvent B ε k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)]
    · exact ENNReal.ofReal_ne_top
    · refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
      rw [inv_lt_one₀ (by positivity)]
      exact Real.one_lt_sqrt_two
  have h0 := measure_limsup_atTop_eq_zero hsum
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
  rw [mem_limsup_iff_frequently_mem, not_frequently] at hω
  exact hω

/-- A rational time in `[t, t + ε)`. -/
theorem exists_nnrat_mem_Ico (t : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℚ≥0, t ≤ (p : ℝ≥0) ∧ ((p : ℝ≥0) : ℝ) < t + ε := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show (t : ℝ) < t + ε by linarith)
  have hq : (0 : ℚ) ≤ q := by exact_mod_cast (t.coe_nonneg.trans h1.le)
  have hc : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = q := by
    have := map_nnratCast NNReal.toRealHom q.toNNRat
    simp only [NNReal.coe_toRealHom] at this
    rw [this, show ((q.toNNRat : ℚ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) from (Rat.cast_nnratCast _).symm,
      Rat.coe_toNNRat q hq]
  refine ⟨q.toNNRat, ?_, by rw [hc]; exact h2⟩
  rw [← NNReal.coe_le_coe, hc]
  exact h1.le

/-- Outside a block event, a continuous path stays below the block level at every time before `2^k`. -/
theorem abs_le_of_not_blockEvent {ω : Ω} (hc : Continuous fun t => B t ω) {c : ℝ} {k : ℕ}
    (hk : ω ∉ blockEvent B c k) {u : ℝ≥0} (hu : u < 2 ^ k) : |B u ω| ≤ c * 2 ^ k := by
  have hcast : ∀ q : ℚ≥0, q ≤ (2 : ℚ≥0) ^ k ↔ (q : ℝ≥0) ≤ 2 ^ k := fun q => by
    rw [← NNRat.cast_le (K := ℝ≥0)]; push_cast; rfl
  have hbdd : BddAbove (Set.range fun i : Set.Iic ((2 : ℚ≥0) ^ k) => ‖B (i : ℚ≥0) ω‖) := by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := 2 ^ k)).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨M, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hM _ ⟨zero_le, (hcast i).1 i.2⟩
  have hlt : ⨆ i : Set.Iic ((2 : ℚ≥0) ^ k), ‖B (i : ℚ≥0) ω‖ < c * 2 ^ k := not_le.1 hk
  by_contra hcon
  push Not at hcon
  have hU : ∀ᶠ s in 𝓝 u, c * 2 ^ k < |B s ω| :=
    (continuous_abs.comp hc).continuousAt.eventually (lt_mem_nhds hcon)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hU
  have hgap : 0 < min δ ((2 : ℝ) ^ k - u) := lt_min hδ (by
    have : (u : ℝ) < ((2 : ℝ≥0) ^ k : ℝ≥0) := by exact_mod_cast hu
    push_cast at this; linarith)
  obtain ⟨q, huq, hqδ⟩ := exists_nnrat_mem_Ico u hgap
  have hq2 : ((q : ℝ≥0) : ℝ) < 2 ^ k := by linarith [min_le_right δ ((2 : ℝ) ^ k - u)]
  have hqk : q ≤ (2 : ℚ≥0) ^ k := (hcast q).2 (by
    have : ((q : ℝ≥0) : ℝ) ≤ ((2 : ℝ≥0) ^ k : ℝ≥0) := by push_cast; exact hq2.le
    exact_mod_cast this)
  have hd : dist (q : ℝ≥0) u < δ := by
    rw [NNReal.dist_eq, abs_lt]
    have : (u : ℝ) ≤ ((q : ℝ≥0) : ℝ) := by exact_mod_cast huq
    constructor <;> linarith [min_le_left δ ((2 : ℝ) ^ k - u)]
  have h1 := hball hd
  have h2 : ‖B (q : ℝ≥0) ω‖ ≤ ⨆ i : Set.Iic ((2 : ℚ≥0) ^ k), ‖B (i : ℚ≥0) ω‖ :=
    le_ciSup (f := fun i : Set.Iic ((2 : ℚ≥0) ^ k) => ‖B (i : ℚ≥0) ω‖) hbdd ⟨q, hqk⟩
  rw [Real.norm_eq_abs] at h2
  linarith

/-- **Brownian sublinearity**: almost surely, for every `ε > 0` there is `C` with `|B_u| ≤ C + ε u` for all
`u ≥ 0`. -/
theorem ae_abs_le_add_mul [IsProbabilityMeasure P] (hB : IsFilteredBrownianReal 𝓕 B P) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∃ C, ∀ u : ℝ≥0, |B u ω| ≤ C + ε * u := by
  have hall : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ᶠ k in atTop, ω ∉ blockEvent B (1 / ((m : ℝ) + 1)) k :=
    ae_all_iff.2 fun m => ae_eventually_not_blockEvent hB (by positivity)
  filter_upwards [hall, hB.1.cont] with ω hω hc ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
  set c : ℝ := 1 / ((m : ℝ) + 1) with hcdef
  have hc0 : 0 < c := by positivity
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hω m)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := 2 ^ k₀)).exists_bound_of_continuousOn
    (continuous_norm.comp hc).continuousOn
  refine ⟨M, fun u => ?_⟩
  have hεu : 0 ≤ ε * u := by positivity
  by_cases hu : u ≤ 2 ^ k₀
  · have : ‖‖B u ω‖‖ ≤ M := hM u ⟨zero_le, hu⟩
    rw [norm_norm, Real.norm_eq_abs] at this
    linarith
  · push Not at hu
    have hex : ∃ k : ℕ, u < 2 ^ k := pow_unbounded_of_one_lt u (by norm_num)
    classical
    set k := Nat.find hex with hkdef
    have hk : u < 2 ^ k := Nat.find_spec hex
    have hkk₀ : k₀ < k := by
      by_contra h
      push Not at h
      exact absurd (hk.trans_le (pow_le_pow_right₀ (by norm_num) h)) (not_lt.2 hu.le)
    have hk1 : (2 : ℝ≥0) ^ (k - 1) ≤ u := by
      have := Nat.find_min hex (show k - 1 < k by omega)
      exact not_lt.1 this
    have hbound := abs_le_of_not_blockEvent hc (hk₀ k hkk₀.le) hk
    have hk1' : (2 : ℝ) ^ (k - 1) ≤ u := by exact_mod_cast hk1
    have hpow : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le⟩)
    have hc2 : 2 * c ≤ ε := by linarith
    calc |B u ω| ≤ c * 2 ^ k := hbound
      _ = 2 * c * 2 ^ (k - 1) := by rw [hpow]; ring
      _ ≤ 2 * c * u := by gcongr
      _ ≤ ε * u := by gcongr
      _ ≤ M + ε * u := by linarith

end InteractingSLE.Zhan
