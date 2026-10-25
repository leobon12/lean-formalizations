import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.SphereInf
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3




 





set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events
open LQGMetric (DistC)

 
def eventCarrier (z : ℂ) (r : ℝ) : Set ℂ :=
  Metric.closedBall z (2 * r) \ Metric.ball z (r / 2)

 
def eventOpen (z : ℂ) (r : ℝ) : Set ℂ :=
  Metric.ball z (2 * r) \ Metric.closedBall z (r / 2)

 
def eventMiddle (z : ℂ) (r : ℝ) : Set ℂ :=
  Metric.ball z (3 * r / 2) \ Metric.closedBall z (3 * r / 4)

 
def eventBoundary (z : ℂ) (r : ℝ) : Set ℂ :=
  Metric.sphere z (r / 2) ∪ Metric.sphere z (2 * r)

 
def InternalBoundaryGeodesic (D : LSCMetric) (z : ℂ) (r : ℝ)
    (P : ℝ → ℂ) (s t : ℝ) : Prop :=
  ∃ (hu : P s ∈ eventCarrier z r) (hv : P t ∈ eventCarrier z r),
    D.IsCurve P s t ∧
    (∀ v ∈ Icc s t, P v ∈ eventCarrier z r) ∧
    P s ∈ eventBoundary z r ∧ P t ∈ eventBoundary z r ∧
    D.len P s t = D.internal (eventCarrier z r) (⟨P s, hu⟩, ⟨P t, hv⟩) ∧
    D.len P s t < ⊤

 
def EndpointLoopAt (D : LSCMetric) (r a θ : ℝ) (u v x : ℂ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ (1 - a) ^ 2 →
    ∃ A : EuclideanAnnulus,
      A.center = x ∧ A.innerRadius = δ * r ∧
      A.outerRadius = Real.sqrt δ * r ∧
      max (OptimalConstants.Ratios.setDist D {x} (Metric.sphere x (δ * r))) (aroundDist D A) ≤
        ENNReal.ofReal (δ ^ θ) * D (u, v)

 
def EventClause1 (D : LSCMetric) (z : ℂ) (r q θ : ℝ) : Prop :=
  ∀ (P : ℝ → ℂ) (s t : ℝ), InternalBoundaryGeodesic D z r P s t →
    ∀ δ : ℝ, 0 < δ → δ ≤ q →
      ∀ x ∈ eventMiddle z r,
        (∃ v ∈ Icc s t, P v ∈ Metric.ball x (δ * r)) →
          ∃ A : EuclideanAnnulus,
            A.center = x ∧ A.innerRadius = δ * r ∧
            A.outerRadius = Real.sqrt δ * r ∧
            aroundDist D A ≤ ENNReal.ofReal (δ ^ θ) * acrossDist D A

 
def EventClause3 (D : LSCMetric) (z : ℂ) (r q a : ℝ) : Prop :=
  ∀ (P : ℝ → ℂ) (s t : ℝ), InternalBoundaryGeodesic D z r P s t →
    ∀ v w : ℝ, 0 < v → v < w → v ∈ Icc s t → w ∈ Icc s t →
      (∀ τ ∈ Icc v w, P τ ∈ Metric.closedBall z r \ Metric.ball z (a * r)) →
      dist (P v) (P w) ≤ q * r

 
def Attained (D D' : LSCMetric) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (C θ : Ioi (0 : ℝ))
    (Cminus Cplus : ℝ) (hCircle : ℝ) : Prop :=
  let Aouter : EuclideanAnnulus := ⟨(z, (3 * r / 2, 2 * r)), by
    have hr : 0 < (r : ℝ) := r.2
    constructor <;> nlinarith⟩
  let Ashort : EuclideanAnnulus := ⟨(z, ((a : ℝ) * r, r)), by
    have hr : 0 < (r : ℝ) := r.2
    have hq : (q : ℝ) < 1 / 100 := q.2.2
    have ha : 1 - (q : ℝ) < a := a.2.1
    have ha1 : (a : ℝ) < 1 := a.2.2
    constructor <;> nlinarith⟩
  EventClause1 D z r q θ ∧
  aroundDist D Aouter ≤
      min (ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * hCircle)))
        (ENNReal.ofReal (Cminus / (2 * Cplus) * (q : ℝ) ^ (-(θ : ℝ))) *
          OptimalConstants.Ratios.setDist D (eventMiddle z r) (eventBoundary z r)) ∧
  EventClause3 D z r q a ∧
  aroundDist D Ashort ≤ ENNReal.ofReal K * acrossDist D Ashort ∧
  (∀ u v : ℂ, u ∈ Metric.sphere z (a * r) →
    v ∈ Metric.sphere z r → dist u v ≤ q * r →
    (∃ A : EuclideanAnnulus, A.center = v ∧ A.innerRadius = q * r ∧
      A.outerRadius = Real.sqrt q * r ∧
      aroundDist D A ≤ ENNReal.ofReal (Cminus / (2 * Cplus)) *
        OptimalConstants.Ratios.setDist D (eventMiddle z r) (eventBoundary z r)) →
    (∃ (P : ℝ → ℂ) (s t : ℝ), OptimalConstants.Ratios.Geodesic D P s t u v ∧
      (∀ τ ∈ Icc s t, P τ ∈ Metric.closedBall z r \ Metric.ball z (a * r)) ∧
      Metric.diam (P '' Icc s t) ≤ r / 100 ∧
      D (u,v) ≤ ENNReal.ofReal ((1-(a : ℝ))⁻¹ * (r : ℝ) ^ (ξ*Q) * Real.exp (ξ*hCircle)) ∧
      EndpointLoopAt D r a θ u v u ∧ EndpointLoopAt D r a θ u v v) →
    D' (u,v) ≤ ENNReal.ofReal C * D (u,v))

 


def AttainedEvent (D D' : DistC → LSCMetric) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (C θ : Ioi (0 : ℝ))
    (Cminus Cplus : ℝ) : Set DistC :=
  {g | ∃ c : ℝ, IsCircleAverage g r z c ∧
    Attained (D g) (D' g) ξ Q z r q a K C θ Cminus Cplus c}

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events
