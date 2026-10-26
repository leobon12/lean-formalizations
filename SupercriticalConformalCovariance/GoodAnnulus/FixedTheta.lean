import SupercriticalConformalCovariance.GoodAnnulus.Literal
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.CarrierHighProb

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory ProbabilityTheory LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

/-- The E1 exponent can be fixed before the target probability `p` is chosen. -/
theorem exists_fixed_theta_E1 (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) :
    ∃ θ : Ioi (0 : ℝ), ∀ p : ℝ, 0 < p → ∃ q₀ : ℝ, 0 < q₀ ∧
      ∀ (q : Ioo (0 : ℝ) (1 / 100)), (q : ℝ) ≤ q₀ →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
          P {ω | ¬ S36Events.EventClause1 (D (h ω)) z r q θ} ≤ ENNReal.ofReal (p / 4) := by
  obtain ⟨M, C, β, lam₀, hM, hC, hβ, hlam₀, heqcut, htail⟩ :=
    dyadic_good_sample_bad_probability ξ Q D hD ((3 : ℝ) / 4)
      (by norm_num) (by norm_num)
  let θ : ℝ := ratioExponent ((3 : ℝ) / 4)
    (ENNReal.ofReal M * ENNReal.ofReal M).toReal / 4
  have hcost0 : (ENNReal.ofReal M * ENNReal.ofReal M) ≠ 0 := by
    exact (ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by linarith : 0 < M)).ne'
      (ENNReal.ofReal_pos.mpr (by linarith : 0 < M)).ne').ne'
  have hcosttop : (ENNReal.ofReal M * ENNReal.ofReal M) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hθ : 0 < θ := div_pos
    (ratioExponent_pos (by norm_num)
      (ENNReal.toReal_pos hcost0 hcosttop)) (by norm_num)
  refine ⟨⟨θ, hθ⟩, ?_⟩
  intro p hp
  obtain ⟨q₀, hq₀, hq16, hqcut, hqrad, hqradSmall, hbudget⟩ :=
    exists_ratio_cutoff hp hC hlam₀
  have hcut : q₀ ≤ scaleCutoff ((3 : ℝ) / 4)
      (ENNReal.ofReal M * ENNReal.ofReal M).toReal := by
    simpa only [heqcut] using hqcut
  refine ⟨q₀, hq₀, ?_⟩
  intro q hqq₀ Ω _ P _ h hh z r
  have hbad : P {ω | ¬ dyadicGoodSample h D ((3 : ℝ) / 4) M q₀ r
      hq₀ r.2 z ω} ≤ ENNReal.ofReal (p / 4) :=
    (htail P h hh q₀ r hq₀ hqcut r.2 z).trans hbudget
  refine (measure_mono ?_).trans hbad
  intro ω hnot hgood
  have hCR : carrierRatioProperty h ω D θ q₀ r z := by
    intro δ hδ hδq x hxlo hxhi Pth T s hs0 hsT hP hPK hgeo h0 hT
      hhit A hAc hAi hAo
    have hratio := carrier_dyadic_ratio_f0 h ω D M hM hq₀
      (hq16.trans (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8))
      hqrad r.2 z hgood hcut hδ hδq x hxlo hxhi
      hs0 hsT hP hPK hgeo h0 hT hhit
    have hAeq : A = annulusAt x (δ * r) (δ ^ ((1 : ℝ) / 2) * r)
      (mul_pos hδ r.2)
      (mul_lt_mul_of_pos_right
        (Real.self_lt_rpow_of_lt_one hδ (lt_of_le_of_lt hδq
          (by linarith : q₀ < 1)) (by norm_num)) r.2) := by
      apply Subtype.ext
      exact Prod.ext hAc (Prod.ext hAi hAo)
    subst A
    exact hratio
  exact hnot (eventClause1_of_carrierRatio h ω D θ q₀ z r hCR q hqq₀)


end SupercriticalConformalCovariance.GoodAnnulus

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

/-- The good-annulus source data with a single exponent chosen from the metric law
before `p`, `k`, the dyadic scale, or the annulus parameters. -/
theorem fixed_theta_literalGood_high_probability (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D) :
    ∃ θ : Ioi (0 : ℝ), ∀ (k p : ℝ), 0 < k → 0 < p → p < 1 →
    ∃ (n : ℕ) (q : Ioo (0 : ℝ) (1 / 100))
      (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)),
      (q : ℝ) = (1 / 2 : ℝ) ^ n ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        LQGMetric.UMeasurableSet (SourceEvent D ξ Q z r q a K θ k) ∧
        ENNReal.ofReal p ≤ P (h ⁻¹' SourceEvent D ξ Q z r q a K θ k) ∧
        ∀ g ∈ SourceEvent D ξ Q z r q a K θ k,
          ∃ c : ℝ, IsCircleAverage g r z c ∧
            LiteralGood (D g) ξ Q z r q a K θ k c := by
  let hw : IsWeakLQGMetric ξ Q D :=
    B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  obtain ⟨θ, hE1fixed⟩ := exists_fixed_theta_E1 ξ Q D hw
  refine ⟨θ, ?_⟩
  intro k p hk hp0 hp1
  have hb : 0 < 1 - p := by linarith
  have he0 : 0 < (1 - p) / 4 := by positivity
  have he1 : (1 - p) / 4 < 1 := by linarith
  obtain ⟨q₁, hq₁, hE1⟩ := hE1fixed (1 - p) hb
  obtain ⟨M₁, M₂, hM₁, hM₂, hE2⟩ :=
    E2_prob ξ Q hQ D hw θ (2 * k) 1 ((1 - p) / 4) he0 he1
  obtain ⟨n, q, hqd, hqq₁, hqM⟩ :=
    exists_dyadic_q_small q₁ (M₂ / k) θ hq₁ θ.2
  have hE2q : M₂ ≤ (2 * k) / (2 * 1) * (q : ℝ) ^ (-(θ : ℝ)) := by
    have hmul : M₂ ≤ k * (q : ℝ) ^ (-(θ : ℝ)) := by
      calc M₂ = k * (M₂ / k) := by field_simp
        _ ≤ k * (q : ℝ) ^ (-(θ : ℝ)) := mul_le_mul_of_nonneg_left hqM hk.le
    have hcoef : (2 * k) / (2 * 1) = k := by ring
    rw [hcoef]
    exact hmul
  obtain ⟨a₀, hE3⟩ := E3_prob ξ Q hQ D hw ((1 - p) / 4) he0 q
  let aval : ℝ := max (a₀ : ℝ) (1 - 1 / (M₁ + 1))
  have hM₁' : 0 < 1 / (M₁ + 1) := by positivity
  have ha1 : aval < 1 := max_lt a₀.2.2 (by linarith)
  have ha0 : 1 - (q : ℝ) < aval := lt_of_lt_of_le a₀.2.1 (le_max_left _ _)
  let a : Ioo (1 - (q : ℝ)) 1 := ⟨aval, ha0, ha1⟩
  have haM : M₁ ≤ (1 - (a : ℝ))⁻¹ := by
    have h1 : 1 - (a : ℝ) ≤ (M₁ + 1)⁻¹ := by
      change 1 - aval ≤ (M₁ + 1)⁻¹
      dsimp [aval]
      have := le_max_right (a₀ : ℝ) (1 - 1 / (M₁ + 1))
      rw [← one_div]
      linarith
    have h2 : 0 < 1 - (a : ℝ) := sub_pos.mpr a.2.2
    have h3 : M₁ + 1 ≤ (1 - (a : ℝ))⁻¹ :=
      (le_inv_comm₀ h2 (show (0 : ℝ) < M₁ + 1 by positivity)).mp h1
    linarith
  obtain ⟨K, hE4⟩ := E4_prob ξ Q D hw a ((1 - p) / 4) he0 he1
  refine ⟨n, q, a, K, hqd, ?_⟩
  intro Ω _ P _ h hh z r
  have h3 : P {ω | ¬ S36Events.EventClause3 (D (h ω)) z r q a} ≤
      ENNReal.ofReal ((1 - p) / 4) := by
    have hsub : {ω | ¬ S36Events.EventClause3 (D (h ω)) z r q a} ⊆
        {ω | ¬ S36Events.EventClause3 (D (h ω)) z r q a₀} := by
      intro ω hω h3'
      exact hω (eventClause3_mono (D (h ω)) z r.2
        (show (a₀ : ℝ) ≤ aval from le_max_left _ _) h3')
    exact (measure_mono hsub).trans (hE3 P h hh z r)
  have hprob := sourceEvent_prob_of_clause_bounds P h hh D hD.1 ξ Q z r q a K θ k p
    hp0 hp1 (hE1 q hqq₁ P h hh z r) (hE2 q a haM hE2q P h hh z r)
    h3 (hE4 P h hh z r)
  refine ⟨sourceEvent_um hD.1 ξ Q z r q a K θ k, hprob, ?_⟩
  intro g hg
  obtain ⟨c, hc, hgood⟩ := hg
  exact ⟨c, hc, sourceGood_implies_literal (D g) ξ Q z r q a K θ k c hgood⟩


end SupercriticalConformalCovariance.GoodAnnulus

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC)
open SupercriticalLQGUniqueness

/-- The paper's exact `p < 1` range; nonpositive targets follow from any positive target. -/
theorem fixed_theta_literalGood_high_probability_lt_one (ξ : Ioi (0 : ℝ))
    (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsStrongLQGMetric ξ Q D) :
    ∃ θ : Ioi (0 : ℝ), ∀ (k p : ℝ), 0 < k → p < 1 →
    ∃ (n : ℕ) (q : Ioo (0 : ℝ) (1 / 100))
      (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)),
      (q : ℝ) = (1 / 2 : ℝ) ^ n ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        LQGMetric.UMeasurableSet (SourceEvent D ξ Q z r q a K θ k) ∧
        ENNReal.ofReal p ≤ P (h ⁻¹' SourceEvent D ξ Q z r q a K θ k) ∧
        ∀ g ∈ SourceEvent D ξ Q z r q a K θ k,
          ∃ c : ℝ, IsCircleAverage g r z c ∧
            LiteralGood (D g) ξ Q z r q a K θ k c := by
  obtain ⟨θ, hθ⟩ := fixed_theta_literalGood_high_probability ξ Q hQ D hD
  refine ⟨θ, ?_⟩
  intro k p hk hp
  let p' : ℝ := (max p 0 + 1) / 2
  have hp'0 : 0 < p' := by
    dsimp [p']
    have := le_max_right p 0
    linarith
  have hp'1 : p' < 1 := by
    dsimp [p']
    have := max_lt hp (by norm_num : (0 : ℝ) < 1)
    linarith
  have hpp' : p ≤ p' := by
    dsimp [p']
    have h1 := le_max_left p 0
    have h2 := max_lt hp (by norm_num : (0 : ℝ) < 1)
    linarith
  obtain ⟨n, q, a, K, hq, hprob⟩ := hθ k p' hk hp'0 hp'1
  refine ⟨n, q, a, K, hq, ?_⟩
  intro Ω _ P _ h hh z r
  obtain ⟨hum, hpbound, hlit⟩ := hprob P h hh z r
  exact ⟨hum, (ENNReal.ofReal_le_ofReal hpp').trans hpbound, hlit⟩


end SupercriticalConformalCovariance.GoodAnnulus
