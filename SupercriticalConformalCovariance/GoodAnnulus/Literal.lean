import SupercriticalConformalCovariance.GoodAnnulus.Bounds
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.Clause5
import SupercriticalLQGUniqueness.B2.PfeLocal.Length

set_option autoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios

/-- The paper's `S`, with the closed annulus carrier required for boundary endpoints. -/
def barrier (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  D.internalSetDist (S36Events.eventCarrier z r)
    (Subtype.val ⁻¹' S36Events.eventMiddle z r)
    (Subtype.val ⁻¹' S36Events.eventBoundary z r)

/-- The ambient set distance in DG's E2 is bounded by the internal barrier `S`. -/
theorem ambient_setDist_le_barrier (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ)) :
    setDist D (S36Events.eventMiddle z r) (S36Events.eventBoundary z r) ≤
      barrier D z r := by
  unfold barrier LSCMetric.internalSetDist
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  calc
    setDist D (S36Events.eventMiddle z r) (S36Events.eventBoundary z r) ≤
        D (x.1, y.1) := iInf₂_le_of_le x.1 hx (iInf₂_le y.1 hy)
    _ ≤ D.internal (S36Events.eventCarrier z r) (x, y) :=
      LSCMetric.edist_le_internal D _ (x, y)

/-- (G1), restricted to the paper's dyadic family `Δ`. -/
def G1 (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (θ : Ioi (0 : ℝ)) : Prop :=
  ∀ (P : ℝ → ℂ) (s t : ℝ), S36Events.InternalBoundaryGeodesic D z r P s t →
    ∀ n : ℕ, (1 / 2 : ℝ) ^ n ≤ (q : ℝ) →
      ∀ x ∈ S36Events.eventMiddle z r,
        (∃ v ∈ Icc s t, P v ∈ Metric.ball x (((1 / 2 : ℝ) ^ n) * r)) →
          ∃ A : EuclideanAnnulus,
            A.center = x ∧ A.innerRadius = ((1 / 2 : ℝ) ^ n) * r ∧
            A.outerRadius = Real.sqrt ((1 / 2 : ℝ) ^ n) * r ∧
            aroundDist D A ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ (θ : ℝ)) * acrossDist D A

/-- (G2), with the paper's internal barrier `S`. -/
def G2 (D : LSCMetric) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (θ : Ioi (0 : ℝ)) (k c : ℝ) : Prop :=
  aroundDist D (outerAnn z r) ≤
    min (ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)))
      (ENNReal.ofReal (k * (q : ℝ) ^ (-(θ : ℝ))) * barrier D z r)

/-- (G3), the full diameter form used in §6. -/
def G3 (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) : Prop :=
  ∀ (P : ℝ → ℂ) (σ τ : ℝ), S36Events.InternalBoundaryGeodesic D z r P σ τ →
    ∀ s t : ℝ, 0 < s → σ ≤ s → t ≤ τ →
      (∀ u ∈ Icc s t, P u ∈ closedBall z r \ ball z ((a : ℝ) * r)) →
      Metric.diam (P '' Icc s t) ≤ (q : ℝ) * r

/-- (G4), the short-annulus loop-to-crossing ratio. -/
def G4 (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ))
    {q : Ioo (0 : ℝ) (1 / 100)} (a : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) : Prop :=
  E4Prop D z r a K

/-- All four literal conditions. -/
def LiteralGood (D : LSCMetric) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) (θ : Ioi (0 : ℝ)) (k c : ℝ) : Prop :=
  G1 D z r q θ ∧ G2 D ξ Q z r q a θ k c ∧ G3 D z r q a ∧ G4 D z r a K

/-- DG's four source clauses imply the paper's four conditions. -/
theorem sourceGood_implies_literal (D : LSCMetric) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k c : ℝ)
    (h : SourceGood D ξ Q z r q a K θ k c) :
    LiteralGood D ξ Q z r q a K θ k c := by
  rcases h with ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, h4⟩
  · intro P s t hP n hn x hx hhit
    exact h1 P s t hP _ (pow_pos (by norm_num) n) hn x hx hhit
  · change E2Prop D ξ Q z r q a θ (2 * k) 1 c at h2
    unfold G2 E2Prop at *
    have hcoef : (2 * k) / (2 * 1) = k := by ring
    rw [hcoef] at h2
    calc
      aroundDist D (outerAnn z r) ≤
          min (ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)))
            (ENNReal.ofReal (k * (q : ℝ) ^ (-(θ : ℝ))) *
              setDist D (S36Events.eventMiddle z r) (S36Events.eventBoundary z r)) := h2
      _ ≤ min (ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)))
            (ENNReal.ofReal (k * (q : ℝ) ^ (-(θ : ℝ))) * barrier D z r) := by
          gcongr
          exact ambient_setDist_le_barrier D z r
  · intro P σ τ hP s t hs hσs htτ hshort
    exact S36Events.EventClause3.diam_le D h3 hP q.2.1.le r.2.le hs hσs htτ hshort


end SupercriticalConformalCovariance.GoodAnnulus

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale

/-- A universally measurable source-only event of probability at least `p` supplies
all four literal conditions, uniformly over centre and radius. -/
theorem literalGood_high_probability (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (k p : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ (θ : Ioi (0 : ℝ)) (n : ℕ) (q : Ioo (0 : ℝ) (1 / 100))
      (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)),
      (q : ℝ) = (1 / 2 : ℝ) ^ n ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        LQGMetric.UMeasurableSet (SourceEvent D ξ Q z r q a K θ k) ∧
        ENNReal.ofReal p ≤ P (h ⁻¹' SourceEvent D ξ Q z r q a K θ k) ∧
        ∀ g ∈ SourceEvent D ξ Q z r q a K θ k,
          ∃ c : ℝ, IsCircleAverage g r z c ∧
            LiteralGood (D g) ξ Q z r q a K θ k c := by
  obtain ⟨θ, n, q, a, K, hq, hprob⟩ := sourceEvent_prob ξ Q hQ D hD k p hk hp0 hp1
  refine ⟨θ, n, q, a, K, hq, ?_⟩
  intro Ω _ P _ h hh z r
  refine ⟨sourceEvent_um hD.1 ξ Q z r q a K θ k, hprob P h hh z r, ?_⟩
  intro g hg
  obtain ⟨c, hc, hgood⟩ := hg
  exact ⟨c, hc, sourceGood_implies_literal (D g) ξ Q z r q a K θ k c hgood⟩


end SupercriticalConformalCovariance.GoodAnnulus
