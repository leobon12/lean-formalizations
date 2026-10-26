import SupercriticalConformalCovariance.GoodAnnulus.FixedTheta
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EScale

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC addConst circleAvg IsWholePlaneGFF IsGFFPlusCont)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

/-- Multiplying the metric by the Weyl factor and shifting the circle average
preserves all four source clauses. -/
theorem sourceGood_scale_iff {d₁ d₂ : LSCMetric} {ξ : ℝ} (t : ℝ)
    (hd : ∀ x y, d₂ (x, y) = ENNReal.ofReal (Real.exp (ξ * t)) * d₁ (x, y))
    (Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) (θ : Ioi (0 : ℝ)) (k c : ℝ) :
    SourceGood d₂ ξ Q z r q a K θ k (c + t) ↔
      SourceGood d₁ ξ Q z r q a K θ k c := by
  set s : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * t))
  have hs0 : s ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hst : s ≠ ⊤ := ENNReal.ofReal_ne_top
  have harnd := SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale
    d₁ d₂ s hs0 hst hd
  have hacr := SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale
    d₁ d₂ s hs0 hst hd
  have hset := setDist_eq_mul_of_scale hs0 hst hd
  unfold SourceGood
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · unfold S36Events.EventClause1
    simp only [ibg_scale_iff hs0 hst hd, harnd, hacr, scale_le_scale_iff hs0 hst]
  · unfold E2Prop
    rw [harnd, hset, ofReal_N_shift, mul_left_comm _ s, min_mul_mul_left]
    exact scale_le_iff hs0 hst _ _
  · unfold S36Events.EventClause3
    simp only [ibg_scale_iff hs0 hst hd]
  · unfold E4Prop
    rw [harnd, hacr]
    exact scale_le_scale_iff hs0 hst _ _ _

/-- The source event is invariant under an additive constant whenever Weyl scaling holds. -/
theorem sourceEvent_addConst_iff (D : DistC → LSCMetric) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) (θ : Ioi (0 : ℝ)) (k : ℝ) (g : DistC) (t : ℝ)
    (hd : ∀ x y, D (addConst g t) (x, y) =
      ENNReal.ofReal (Real.exp (ξ * t)) * D g (x, y)) :
    addConst g t ∈ SourceEvent D ξ Q z r q a K θ k ↔
      g ∈ SourceEvent D ξ Q z r q a K θ k := by
  constructor
  · rintro ⟨c', hc', hgood⟩
    refine ⟨c' - t, ?_, ?_⟩
    · have h := isCircleAverage_addConst g t r z (c' - t)
      rw [sub_add_cancel] at h
      exact h.mp hc'
    · have h := sourceGood_scale_iff (d₁ := D g) (d₂ := D (addConst g t))
        t hd Q z r q a K θ k (c' - t)
      rw [sub_add_cancel] at h
      exact h.mp hgood
  · rintro ⟨c, hc, hgood⟩
    exact ⟨c + t, (isCircleAverage_addConst g t r z c).mpr hc,
      (sourceGood_scale_iff (d₁ := D g) (d₂ := D (addConst g t))
        t hd Q z r q a K θ k c).mpr hgood⟩

/-- Additive-constant invariance on a whole-plane GFF, for any measurable random constant. -/
theorem ae_sourceEvent_addConst_iff {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsStrongLQGMetric ξ Q D) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) (θ : Ioi (0 : ℝ)) (k : ℝ) (t : Ω → ℝ) :
    ∀ᵐ ω ∂P, (addConst (h ω) (t ω) ∈ SourceEvent D ξ Q z r q a K θ k ↔
      h ω ∈ SourceEvent D ξ Q z r q a K θ k) := by
  let hw : IsWeakLQGMetric ξ Q D :=
    B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  have hh' : IsGFFPlusCont h P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh
  filter_upwards [SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.ae_addConst_eq_mul
    P h hh' ξ Q D hw t] with ω hω
  exact sourceEvent_addConst_iff D ξ Q z r q a K θ k (h ω) (t ω)
    (fun x y => hω (x, y))


end SupercriticalConformalCovariance.GoodAnnulus

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC addConst circleAvg IsWholePlaneGFF)
open SupercriticalLQGUniqueness

/-- Subtracting the unit-circle average normalizes any whole-plane GFF. -/
theorem normalized_by_circleAverage {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    IsNormalizedWholePlaneGFF
      (fun ω => addConst (h ω) (-circleAvg (h ω) 1 0)) P := by
  let a : Ω → ℝ := fun ω => circleAvg (h ω) 1 0
  have ha : Measurable a :=
    (LQGMetric.measurable_circleAvg_left 1 0).comp hh.measurable
  have hk : IsWholePlaneGFF (fun ω => addConst (h ω) (-(a ω))) P :=
    hh.addConst ha.neg
  refine isNormalizedWholePlaneGFF_iff_old.mpr ⟨hk, ?_⟩
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
  change circleAvg (addConst (h ω) (-(a ω))) 1 0 = 0
  rw [hω (-(a ω))]
  exact add_neg_cancel _

/-- The source good-annulus event and all four conditions for any whole-plane
GFF, including one with a random additive constant. -/
theorem wholePlane_literalGood_high_probability (ξ : Ioi (0 : ℝ))
    (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsStrongLQGMetric ξ Q D) :
    ∃ θ : Ioi (0 : ℝ), ∀ (k p : ℝ), 0 < k → p < 1 →
    ∃ (n : ℕ) (q : Ioo (0 : ℝ) (1 / 100))
      (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)),
      (q : ℝ) = (1 / 2 : ℝ) ^ n ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        LQGMetric.UMeasurableSet (SourceEvent D ξ Q z r q a K θ k) ∧
        ENNReal.ofReal p ≤ P (h ⁻¹' SourceEvent D ξ Q z r q a K θ k) ∧
        ∀ g ∈ SourceEvent D ξ Q z r q a K θ k,
          ∃ c : ℝ, IsCircleAverage g r z c ∧
            LiteralGood (D g) ξ Q z r q a K θ k c := by
  obtain ⟨θ, hθ⟩ := fixed_theta_literalGood_high_probability_lt_one ξ Q hQ D hD
  refine ⟨θ, ?_⟩
  intro k p hk hp
  obtain ⟨n, q, a, K, hqd, hprob⟩ := hθ k p hk hp
  refine ⟨n, q, a, K, hqd, ?_⟩
  intro Ω _ P _ h hh z r
  let t : Ω → ℝ := fun ω => -circleAvg (h ω) 1 0
  let hN : Ω → DistC := fun ω => addConst (h ω) (t ω)
  have hhN : IsNormalizedWholePlaneGFF hN P := normalized_by_circleAverage P h hh
  obtain ⟨_, hpN, _⟩ := hprob P hN hhN z r
  have heq : (hN ⁻¹' SourceEvent D ξ Q z r q a K θ k) =ᵐ[P]
      (h ⁻¹' SourceEvent D ξ Q z r q a K θ k) := by
    filter_upwards [ae_sourceEvent_addConst_iff P h hh ξ Q D hD z r q a K θ k t]
      with ω hω
    exact propext hω
  refine ⟨sourceEvent_um hD.1 ξ Q z r q a K θ k, ?_, ?_⟩
  · exact hpN.trans_eq (measure_congr heq)
  · intro g hg
    obtain ⟨c, hc, hgood⟩ := hg
    exact ⟨c, hc, sourceGood_implies_literal (D g) ξ Q z r q a K θ k c hgood⟩


end SupercriticalConformalCovariance.GoodAnnulus
