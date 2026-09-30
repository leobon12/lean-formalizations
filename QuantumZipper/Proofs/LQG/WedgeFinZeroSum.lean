import QuantumZipper.Proofs.LQG.WedgeFinZeroMoment
import QuantumZipper.Proofs.LQG.MeasurabilityAE
import QuantumZipper.Proofs.LQG.LogSingGood

/-!
# WEDGE-FIN0, part 3: `∫_{B(0,1) ∩ ℍ} ‖z‖^{−αγ} dμ_X < ∞` almost surely, for `α < Q`

The area analogue at the boundary point `0` of `LogSingGood.ae_summable_tail_offsets`:

* `ae_tsum_lt_top_of_moment`: summable fractional moments `E T_m^q ≤ a b^m`, `b < 1`, give
  `Σ_m T_m < ∞` a.s. (as `(Σ T_m)^q ≤ Σ T_m^q`, `q ≤ 1`);
* `ae_tsum_wgt_lt_top`: a.s. `Σ_m 2^{(m+6)α⁺γ} μ_Z(B(0,2^{-m-5}) ∩ ℍ) < ∞`, with the moment bound
  `WedgeFinZero.lintegral_ball_rpow_le` at `p' = min(p, (Q − α⁺)/(2γ))`, `p = 1/2 + (4 − γ²)/16`;
* `ae_withDensity_ball_lt_top`: a.s. `∫_{B(0,1) ∩ ℍ} ‖z‖^{−αγ} dμ_X < ∞` (pointwise
  `‖z‖^{−αγ} ≤ 2^{5α⁺γ} + Σ_m 2^{(m+6)α⁺γ} 1_{B(0,2^{-m-5})}(z)` on the unit half-disc);
* `ae_logSing_ball_lt_top`: a.s. `X + α(−log‖·‖)` is good and has finite area on `B(0,1) ∩ ℍ`
  (its area measure is `‖z‖^{−αγ} μ_X`, `LogSingGood.hasAreaLimit_add_Lf`).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), §3 (fractional moments of the bulk
measure); Sheffield, arXiv:1012.4797, §1.6, p. 21 (finite `µ_h` mass near `0` for `α < Q`). The
dyadic summation is the one of `LogSingGood.ae_summable_tail_offsets`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace WedgeFinZero

open FinArea

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Summation from fractional moments. -/
theorem ae_tsum_lt_top_of_moment {T : ℕ → Ω → ℝ≥0∞} (hT : ∀ m, AEMeasurable (T m) P)
    {q a b : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (h : ∀ m, ∫⁻ ω, T m ω ^ q ∂P ≤ ENNReal.ofReal (a * b ^ m)) :
    ∀ᵐ ω ∂P, ∑' m, T m ω < ⊤ := by
  have hm : ∀ m, AEMeasurable (fun ω => T m ω ^ q) P := fun m => (hT m).pow_const q
  have hsum : ∫⁻ ω, ∑' m, T m ω ^ q ∂P ≠ ⊤ := by
    rw [lintegral_tsum hm]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg ha (pow_nonneg hb0 m))
      ((summable_geometric_of_lt_one hb0 hb1).mul_left a)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hm) hsum] with ω hω
  have h1 : (∑' m, T m ω) ^ q < ⊤ := (FracMom.rpow_tsum_le_tsum_rpow _ hq0 hq1).trans_lt hω
  exact (ENNReal.rpow_lt_top_iff_of_pos hq0).1 h1

/-- The weights `2^{(m+6) α⁺ γ}`. -/
def wgt (γ α : ℝ) (m : ℕ) : ℝ := radius (m + 6) ^ (-(max α 0 * γ))

theorem wgt_rpow_eq (γ α p' : ℝ) (m : ℕ) :
    wgt γ α m ^ p' = exp (((m : ℝ) + 6) * log 2 * max α 0 * γ * p') := by
  rw [wgt, ← rpow_mul (radius_pos _).le, rpow_def_of_pos (radius_pos _), log_radius]
  congr 1; push_cast; ring

/-- **A.s. summability of the weighted masses near `0`.** -/
theorem ae_tsum_wgt_lt_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    ∀ᵐ ω ∂P, ∑' m, ENNReal.ofReal (wgt γ α m) *
      qAreaMeasure γ (AreaExist.aZ X 2 ω) (Metric.ball 0 (radius (m + 5)) ∩ H) < ⊤ := by
  set αp := max α 0 with hαp
  have hQ : γ * Qc γ = 2 + γ ^ 2 / 2 := by unfold Qc; field_simp
  have hQpos : 0 < Qc γ := by unfold Qc; positivity
  have hαQ : αp < Qc γ := max_lt hα hQpos
  set η : ℝ := (4 - γ ^ 2) / 16 with hη
  set p : ℝ := 1 / 2 + η with hp
  have hγ4 : γ ^ 2 < 4 := by nlinarith
  have hη0 : 0 < η := by rw [hη]; linarith
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp1 : p ≤ 1 := by rw [hp, hη]; nlinarith
  have he : 1 < eA γ p := by
    have : eA γ p - 1 = η * (4 - γ ^ 2) * (1 / 2 - γ ^ 2 / 16) := by rw [eA, hp, hη]; ring
    have h1 : 0 < 4 - γ ^ 2 := by linarith
    have h2 : 0 < 1 / 2 - γ ^ 2 / 16 := by linarith
    nlinarith [mul_pos (mul_pos hη0 h1) h2]
  set p' := min p ((Qc γ - αp) / (2 * γ)) with hp'
  have hp'0 : 0 < p' := lt_min hp0 (div_pos (by linarith) (by linarith))
  have hp'p : p' ≤ p := min_le_left _ _
  have hp'γ : 2 * γ * p' ≤ Qc γ - αp := by
    have := min_le_right p ((Qc γ - αp) / (2 * γ))
    rw [le_div_iff₀ (by linarith)] at this; linarith
  set rate := log 2 * (eA γ p' - αp * γ * p') with hrate
  have hrate0 : 0 < rate := by
    have hL := log_pos one_lt_two
    have hid : eA γ p' - αp * γ * p' = p' * (γ * (Qc γ - αp) - p' * γ ^ 2) := by
      rw [eA]; linear_combination (-p') * hQ
    have hpos : 0 < γ * (Qc γ - αp) - p' * γ ^ 2 := by
      have h1 : γ * (2 * γ * p') ≤ γ * (Qc γ - αp) := mul_le_mul_of_nonneg_left hp'γ hγ.le
      have h2 : 0 < γ * (Qc γ - αp) := mul_pos hγ (by linarith)
      nlinarith
    rw [hrate, hid]
    exact mul_pos hL (mul_pos hp'0 hpos)
  set K := cS γ p ^ (p' / p) * exp (log 2 * p' ^ 2 * γ ^ 2 + 6 * log 2 * αp * γ * p') with hK
  have hcS : 0 ≤ cS γ p := by
    have hq1 : qR γ p < 1 := Real.exp_lt_one_iff.2 (by nlinarith [log_pos one_lt_two])
    rw [cS]; exact mul_nonneg (by positivity) (inv_nonneg.2 (by linarith))
  have hK0 : 0 ≤ K := mul_nonneg (rpow_nonneg hcS _) (exp_pos _).le
  have hXm : ∀ μ, Measurable fun ω => AreaExist.aZ X 2 ω μ := fun μ =>
    (measurable_pi_apply μ).comp (AreaExist.measurable_aZ hX 2)
  have hS : ∀ m : ℕ, MeasurableSet (Metric.ball (0 : ℂ) (radius (m + 5)) ∩ H) := fun m =>
    Metric.isOpen_ball.measurableSet.inter isOpen_H.measurableSet
  refine ae_tsum_lt_top_of_moment (q := p') (a := K) (b := exp (-rate))
    (fun m => (LQGMeasAE.aemeasurable_qAreaMeasure_apply_of_ae hXm
      (AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 2) (hS m)).const_mul _)
    hp'0 (hp'p.trans hp1) hK0 (exp_pos _).le (Real.exp_lt_one_iff.2 (by linarith)) fun m => ?_
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp'0.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp'0.le ENNReal.ofReal_ne_top)]
  calc ENNReal.ofReal (wgt γ α m) ^ p' * ∫⁻ ω,
        qAreaMeasure γ (AreaExist.aZ X 2 ω) (Metric.ball 0 (radius (m + 5)) ∩ H) ^ p' ∂P
      ≤ ENNReal.ofReal (wgt γ α m) ^ p' * ENNReal.ofReal (cS γ p ^ (p' / p) *
          (exp (log 2 * p' ^ 2 * γ ^ 2) * exp (-(log 2 * eA γ p')) ^ m)) := by
        gcongr; exact lintegral_ball_rpow_le hX hγ hγ2 hp0 hp1 he hp'0 hp'p m
    _ = ENNReal.ofReal (K * exp (-rate) ^ m) := by
        have hw0 : 0 ≤ wgt γ α m := rpow_nonneg (radius_pos _).le _
        rw [ENNReal.ofReal_rpow_of_nonneg hw0 hp'0.le,
          ← ENNReal.ofReal_mul (rpow_nonneg hw0 _), wgt_rpow_eq]
        congr 1
        rw [hK, ← exp_nat_mul, ← exp_nat_mul]
        calc exp (((m : ℝ) + 6) * log 2 * αp * γ * p') * (cS γ p ^ (p' / p) *
              (exp (log 2 * p' ^ 2 * γ ^ 2) * exp (↑m * -(log 2 * eA γ p'))))
            = cS γ p ^ (p' / p) * exp (((m : ℝ) + 6) * log 2 * αp * γ * p' +
                log 2 * p' ^ 2 * γ ^ 2 + ↑m * -(log 2 * eA γ p')) := by
              rw [exp_add, exp_add]; ring
          _ = cS γ p ^ (p' / p) * exp ((log 2 * p' ^ 2 * γ ^ 2 + 6 * log 2 * αp * γ * p') +
                ↑m * -rate) := by
              congr 2; rw [hrate]; ring
          _ = _ := by rw [exp_add]; ring

/-- Pointwise domination of `‖z‖^{−αγ}` on the unit half-disc. -/
theorem ofReal_norm_rpow_le {γ α : ℝ} (hγ : 0 < γ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1 ∩ H) :
    ENNReal.ofReal (‖z‖ ^ (-(α * γ))) ≤ ENNReal.ofReal (radius 5 ^ (-(max α 0 * γ))) +
      ∑' m, ENNReal.ofReal (wgt γ α m) *
        (Metric.ball (0 : ℂ) (radius (m + 5)) ∩ H).indicator 1 z := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 fun h => by
    have : (0 : ℝ) < z.im := hz.2
    rw [h] at this; simp at this
  have hz1 : ‖z‖ < 1 := by simpa using hz.1
  have hexp : -(max α 0 * γ) ≤ 0 := neg_nonpos.2 (mul_nonneg (le_max_right _ _) hγ.le)
  have h1 : ‖z‖ ^ (-(α * γ)) ≤ ‖z‖ ^ (-(max α 0 * γ)) :=
    rpow_le_rpow_of_exponent_ge hz0 hz1.le
      (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _) hγ.le))
  by_cases h5 : radius 5 ≤ ‖z‖
  · refine le_trans ?_ le_self_add
    exact ENNReal.ofReal_le_ofReal (h1.trans (rpow_le_rpow_of_nonpos (radius_pos 5) h5 hexp))
  · push Not at h5
    have hex : ∃ n, radius (n + 6) ≤ ‖z‖ := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hz0 (by norm_num : (2 : ℝ)⁻¹ < 1)
      exact ⟨k, (AreaExist.aradius_anti (by omega)).trans hk.le⟩
    set n := Nat.find hex
    have hn : radius (n + 6) ≤ ‖z‖ := Nat.find_spec hex
    have hn5 : ‖z‖ < radius (n + 5) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0]; exact h5
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hpos.ne'
        have := Nat.find_min hex (show k < n by omega)
        rw [hk]; push Not at this
        rwa [show k + 1 + 5 = k + 6 by omega]
    refine le_trans ?_ le_add_self
    refine le_trans ?_ (ENNReal.le_tsum n)
    have hmem : z ∈ Metric.ball (0 : ℂ) (radius (n + 5)) ∩ H := ⟨by simpa using hn5, hz.2⟩
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    exact ENNReal.ofReal_le_ofReal (h1.trans (rpow_le_rpow_of_nonpos (radius_pos _) hn hexp))

/-- **A.s. `∫_{B(0,1) ∩ ℍ} ‖z‖^{−αγ} dμ_X < ∞`** for `α < Q`. -/
theorem ae_withDensity_ball_lt_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    ∀ᵐ ω ∂P, (qAreaMeasure γ (X ω)).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(α * γ))))
      (Metric.ball 0 1 ∩ H) < ⊤ := by
  filter_upwards [ae_tsum_wgt_lt_top hX (P := P) hγ hγ2 hα,
    ae_qAreaMeasure_aZ_eq_smul hX (P := P) hγ hγ2 2,
    ae_qAreaMeasure_ball_lt_top hX (P := P) hγ hγ2] with ω hs he hb
  set μ := qAreaMeasure γ (X ω)
  set c := ENNReal.ofReal (exp (-(γ * X ω (foldedCircle 0 2))))
  have hc : c ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact exp_pos _
  have hU : ∀ m : ℕ, MeasurableSet (Metric.ball (0 : ℂ) (radius (m + 5)) ∩ H) := fun m =>
    Metric.isOpen_ball.measurableSet.inter isOpen_H.measurableSet
  have hS : MeasurableSet (Metric.ball (0 : ℂ) 1 ∩ H) :=
    Metric.isOpen_ball.measurableSet.inter isOpen_H.measurableSet
  rw [he] at hs
  simp only [Measure.smul_apply, smul_eq_mul] at hs
  have hs' : ∑' m, ENNReal.ofReal (wgt γ α m) * μ (Metric.ball 0 (radius (m + 5)) ∩ H) < ⊤ := by
    have e : ∑' m, ENNReal.ofReal (wgt γ α m) * (c * μ (Metric.ball 0 (radius (m + 5)) ∩ H)) =
        c * ∑' m, ENNReal.ofReal (wgt γ α m) * μ (Metric.ball 0 (radius (m + 5)) ∩ H) := by
      rw [← ENNReal.tsum_mul_left]; congr 1; funext m; ring
    rw [e] at hs
    exact ENNReal.lt_top_of_mul_ne_top_right hs.ne hc
  rw [withDensity_apply _ hS]
  calc ∫⁻ z in Metric.ball 0 1 ∩ H, ENNReal.ofReal (‖z‖ ^ (-(α * γ))) ∂μ
      ≤ ∫⁻ z in Metric.ball 0 1 ∩ H, (ENNReal.ofReal (radius 5 ^ (-(max α 0 * γ))) +
          ∑' m, ENNReal.ofReal (wgt γ α m) *
            (Metric.ball (0 : ℂ) (radius (m + 5)) ∩ H).indicator 1 z) ∂μ :=
        setLIntegral_mono' hS fun z hz => ofReal_norm_rpow_le hγ hz
    _ = ENNReal.ofReal (radius 5 ^ (-(max α 0 * γ))) * μ (Metric.ball 0 1 ∩ H) +
          ∫⁻ z in Metric.ball 0 1 ∩ H, ∑' m, ENNReal.ofReal (wgt γ α m) *
            (Metric.ball (0 : ℂ) (radius (m + 5)) ∩ H).indicator 1 z ∂μ := by
        rw [lintegral_add_left measurable_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal (radius 5 ^ (-(max α 0 * γ))) * μ (Metric.ball 0 1 ∩ H) +
          ∑' m, ENNReal.ofReal (wgt γ α m) * μ (Metric.ball 0 (radius (m + 5)) ∩ H) := by
        gcongr
        refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
        rw [lintegral_tsum (f := fun m z => ENNReal.ofReal (wgt γ α m) *
          (Metric.ball (0 : ℂ) (radius (m + 5)) ∩ H).indicator 1 z)
          fun m => ((measurable_one.indicator (hU m)).const_mul _).aemeasurable]
        congr 1; funext m
        rw [lintegral_const_mul _ (measurable_one.indicator (hU m)),
          lintegral_indicator_one (hU m)]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hb 1), hs'⟩

/-- **The analytic input of WEDGE-FIN0.** Almost surely `X + α(−log‖·‖)` is good and has finite
area on the unit half-disc, for `0 < γ < 2` and `α < Q`. -/
theorem ae_logSing_ball_lt_top {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    ∀ᵐ ω ∂P, IsLQGGood γ (X ω + ofFun fun z => α * -Real.log ‖z‖) ∧
      qAreaMeasure γ (X ω + ofFun fun z => α * -Real.log ‖z‖) (Metric.ball 0 1 ∩ H) < ⊤ := by
  filter_upwards [LogSingGood.logSingGoodAS_holds hγ hγ2 hα Ω _ P X inferInstance hX,
    AreaOffsets.ae_isLQGGood hX hγ hγ2, ae_withDensity_ball_lt_top hX (P := P) hγ hγ2 hα]
    with ω hL hg hw
  refine ⟨hL, ?_⟩
  obtain ⟨F, hF⟩ := hg.1
  have hA := LogSingGood.hasAreaLimit_add_Lf hF hg.qAreaMeasure_spec α
  have e : (X ω + ofFun fun z => α * -Real.log ‖z‖) = X ω + ofFun (LogSingGood.Lf α) := rfl
  rw [e, GoodSample.qAreaMeasure_eq_of_hasAreaLimit ⟨_, LogSingGood.regular_add_Lf hF α⟩ hA]
  exact hw

end WedgeFinZero
end QuantumZipper
