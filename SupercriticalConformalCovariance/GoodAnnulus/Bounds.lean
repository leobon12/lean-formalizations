import SupercriticalConformalCovariance.GoodAnnulus.Source

set_option autoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

/-- Uniform source-clause failure bounds with the paper's parameter order. -/
theorem exists_source_clause_bounds (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (k p : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ (θ : Ioi (0 : ℝ)) (n : ℕ) (q : Ioo (0 : ℝ) (1 / 100))
      (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)),
      (q : ℝ) = (1 / 2 : ℝ) ^ n ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        P {ω | ¬ S36Events.EventClause1 (D (h ω)) z r q θ} ≤
          ENNReal.ofReal ((1 - p) / 4) ∧
        P {ω | ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
          E2Prop (D (h ω)) ξ Q z r q a θ (2 * k) 1 c} ≤
          ENNReal.ofReal ((1 - p) / 4) ∧
        P {ω | ¬ S36Events.EventClause3 (D (h ω)) z r q a} ≤
          ENNReal.ofReal ((1 - p) / 4) ∧
        P {ω | ¬ E4Prop (D (h ω)) z r a K} ≤
          ENNReal.ofReal ((1 - p) / 4) := by
  let hw : IsWeakLQGMetric ξ Q D :=
    B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  have hb : 0 < 1 - p := by linarith
  have he0 : 0 < (1 - p) / 4 := by positivity
  have he1 : (1 - p) / 4 < 1 := by linarith
  obtain ⟨θ, q₁, hq₁, hE1⟩ := E1_prob ξ Q D hw (1 - p) hb
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
    have h2 : 0 < 1 - (a : ℝ) := by exact sub_pos.mpr a.2.2
    have h3 : M₁ + 1 ≤ (1 - (a : ℝ))⁻¹ :=
      (le_inv_comm₀ h2 (show (0 : ℝ) < M₁ + 1 by positivity)).mp h1
    linarith
  obtain ⟨K, hE4⟩ := E4_prob ξ Q D hw a ((1 - p) / 4) he0 he1
  refine ⟨θ, n, q, a, K, hqd, ?_⟩
  intro Ω _ P _ h hh z r
  have h3 : P {ω | ¬ S36Events.EventClause3 (D (h ω)) z r q a} ≤
      ENNReal.ofReal ((1 - p) / 4) := by
    have hsub : {ω | ¬ S36Events.EventClause3 (D (h ω)) z r q a} ⊆
        {ω | ¬ S36Events.EventClause3 (D (h ω)) z r q a₀} := by
      intro ω hω h3'
      exact hω (eventClause3_mono (D (h ω)) z r.2
        (show (a₀ : ℝ) ≤ aval from le_max_left _ _) h3')
    exact (measure_mono hsub).trans (hE3 P h hh z r)
  exact ⟨hE1 q hqq₁ P h hh z r,
    hE2 q a haM hE2q P h hh z r,
    h3, hE4 P h hh z r⟩


end SupercriticalConformalCovariance.GoodAnnulus

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

/-- Four uniform clause bounds imply the source-only joint probability bound. -/
theorem sourceEvent_prob_of_clause_bounds {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (D : DistC → LSCMetric) (hD : Measurable D)
    (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) (θ : Ioi (0 : ℝ)) (k p : ℝ)
    (_hp0 : 0 < p) (hp1 : p < 1)
    (h1 : P {ω | ¬ S36Events.EventClause1 (D (h ω)) z r q θ} ≤
      ENNReal.ofReal ((1 - p) / 4))
    (h2 : P {ω | ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
      E2Prop (D (h ω)) ξ Q z r q a θ (2 * k) 1 c} ≤ ENNReal.ofReal ((1 - p) / 4))
    (h3 : P {ω | ¬ S36Events.EventClause3 (D (h ω)) z r q a} ≤
      ENNReal.ofReal ((1 - p) / 4))
    (h4 : P {ω | ¬ E4Prop (D (h ω)) z r a K} ≤
      ENNReal.ofReal ((1 - p) / 4)) :
    ENNReal.ofReal p ≤ P (h ⁻¹' SourceEvent D ξ Q z r q a K θ k) := by
  let E : Set Ω := h ⁻¹' SourceEvent D ξ Q z r q a K θ k
  let B0 : Set Ω := {ω | ¬ ∃ c : ℝ, IsCircleAverage (h ω) r z c}
  let B1 : Set Ω := {ω | ¬ S36Events.EventClause1 (D (h ω)) z r q θ}
  let B2 : Set Ω := {ω | ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
    E2Prop (D (h ω)) ξ Q z r q a θ (2 * k) 1 c}
  let B3 : Set Ω := {ω | ¬ S36Events.EventClause3 (D (h ω)) z r q a}
  let B4 : Set Ω := {ω | ¬ E4Prop (D (h ω)) z r a K}
  have hnull : NullMeasurableSet E P :=
    (sourceEvent_um hD ξ Q z r q a K θ k).nullMeasurableSet_preimage hh.1.measurable.aemeasurable
  have h0 : P B0 = 0 := by
    have := ae_exists_circleAverage hh.1 r z
    rwa [ae_iff] at this
  have hcover : Eᶜ ⊆ (((B0 ∪ B1) ∪ B2) ∪ B3) ∪ B4 := by
    intro ω hω
    by_contra hn
    have hca : ∃ c : ℝ, IsCircleAverage (h ω) r z c := by
      by_contra hc
      exact hn (Or.inl (Or.inl (Or.inl (Or.inl hc))))
    have hg1 : S36Events.EventClause1 (D (h ω)) z r q θ := by
      by_contra hc
      exact hn (Or.inl (Or.inl (Or.inl (Or.inr hc))))
    have hg2 : ∀ c : ℝ, IsCircleAverage (h ω) r z c →
        E2Prop (D (h ω)) ξ Q z r q a θ (2 * k) 1 c := by
      by_contra hc
      exact hn (Or.inl (Or.inl (Or.inr hc)))
    have hg3 : S36Events.EventClause3 (D (h ω)) z r q a := by
      by_contra hc
      exact hn (Or.inl (Or.inr hc))
    have hg4 : E4Prop (D (h ω)) z r a K := by
      by_contra hc
      exact hn (Or.inr hc)
    obtain ⟨c, hc⟩ := hca
    apply hω
    exact ⟨c, hc, hg1, hg2 c hc, hg3, hg4⟩
  have hbad : P Eᶜ ≤ ENNReal.ofReal (1 - p) := by
    calc
      P Eᶜ ≤ P ((((B0 ∪ B1) ∪ B2) ∪ B3) ∪ B4) := measure_mono hcover
      _ ≤ (((P B0 + P B1) + P B2) + P B3) + P B4 := by
        calc
          P ((((B0 ∪ B1) ∪ B2) ∪ B3) ∪ B4) ≤
              P (((B0 ∪ B1) ∪ B2) ∪ B3) + P B4 := measure_union_le _ _
          _ ≤ (P ((B0 ∪ B1) ∪ B2) + P B3) + P B4 :=
            by
              gcongr
              exact measure_union_le ((B0 ∪ B1) ∪ B2) B3
          _ ≤ ((P (B0 ∪ B1) + P B2) + P B3) + P B4 :=
            by
              gcongr
              exact measure_union_le (B0 ∪ B1) B2
          _ ≤ (((P B0 + P B1) + P B2) + P B3) + P B4 :=
            by
              gcongr
              exact measure_union_le B0 B1
      _ ≤ (((0 + ENNReal.ofReal ((1 - p) / 4)) + ENNReal.ofReal ((1 - p) / 4)) +
          ENNReal.ofReal ((1 - p) / 4)) + ENNReal.ofReal ((1 - p) / 4) := by
        rw [h0]
        gcongr
      _ = ENNReal.ofReal (1 - p) := by
        have he : 0 ≤ (1 - p) / 4 := by linarith
        rw [zero_add, ← ENNReal.ofReal_add he he,
          ← ENNReal.ofReal_add (by linarith : 0 ≤ (1 - p) / 4 + (1 - p) / 4) he,
          ← ENNReal.ofReal_add (by linarith : 0 ≤ (1 - p) / 4 + (1 - p) / 4 + (1 - p) / 4) he]
        congr 1
        ring
  have hreal : ENNReal.ofReal p = 1 - ENNReal.ofReal (1 - p) := by
    calc
      ENNReal.ofReal p = ENNReal.ofReal (1 - (1 - p)) := by congr 1; ring
      _ = 1 - ENNReal.ofReal (1 - p) := by
        simpa only [ENNReal.ofReal_one] using
          (ENNReal.ofReal_sub 1 (q := 1 - p) (by linarith : 0 ≤ 1 - p))
  calc
    ENNReal.ofReal p = 1 - ENNReal.ofReal (1 - p) := hreal
    _ ≤ 1 - P Eᶜ := tsub_le_tsub_left hbad 1
    _ = P E := by simpa only [compl_compl] using
      (prob_compl_eq_one_sub₀ hnull.compl).symm
    _ = P (h ⁻¹' SourceEvent D ξ Q z r q a K θ k) := rfl


end SupercriticalConformalCovariance.GoodAnnulus

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

/-- The four source-only DG clauses hold jointly with probability at least `p`, uniformly
in the centre and radius, for every strong metric coupled to a normalized whole-plane GFF. -/
theorem sourceEvent_prob (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (k p : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ (θ : Ioi (0 : ℝ)) (n : ℕ) (q : Ioo (0 : ℝ) (1 / 100))
      (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)),
      (q : ℝ) = (1 / 2 : ℝ) ^ n ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        ENNReal.ofReal p ≤ P (h ⁻¹' SourceEvent D ξ Q z r q a K θ k) := by
  obtain ⟨θ, n, q, a, K, hdyadic, hbounds⟩ :=
    exists_source_clause_bounds ξ Q hQ D hD k p hk hp0 hp1
  refine ⟨θ, n, q, a, K, hdyadic, ?_⟩
  intro Ω _ P _ h hh z r
  obtain ⟨h1, h2, h3, h4⟩ := hbounds P h hh z r
  exact sourceEvent_prob_of_clause_bounds P h hh D hD.1 ξ Q z r q a K θ k p
    hp0 hp1 h1 h2 h3 h4


end SupercriticalConformalCovariance.GoodAnnulus
