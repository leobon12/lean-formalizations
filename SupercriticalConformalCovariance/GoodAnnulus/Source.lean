import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.E3Clause
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.L34E24
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.E1Clause
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.S36
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong

set_option autoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

/-- DG's four source clauses.  The second clause uses the stronger ambient set distance
from DG; this implies the source paper's internal barrier bound. -/
def SourceGood (D : LSCMetric) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k c : ℝ) : Prop :=
  S36Events.EventClause1 D z r q θ ∧
  S36.E2Prop D ξ Q z r q a θ (2 * k) 1 c ∧
  S36Events.EventClause3 D z r q a ∧
  S36.E4Prop D z r a K

/-- Field event for the source-only clauses, retaining a genuine circle average. -/
def SourceEvent (D : DistC → LSCMetric) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k : ℝ) : Set DistC :=
  {g | ∃ c : ℝ, IsCircleAverage g r z c ∧
    SourceGood (D g) ξ Q z r q a K θ k c}

/-- The source-only field event is universally measurable. -/
theorem sourceEvent_um {D : DistC → LSCMetric} (hD : Measurable D)
    (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k : ℝ) :
    LQGMetric.UMeasurableSet (SourceEvent D ξ Q z r q a K θ k) := by
  have h1 := S36.E1set_um hD z θ r.2 (q.2.2.trans (by norm_num : (1 / 100 : ℝ) < 1))
  have h2 := S36.E2all_um hD ξ Q z r q a θ (2 * k) 1
  have h3 := S36.E3set_um hD z a r.2 q.2.1
  have h4 := LQGMetric.UMeasurableSet.of_measurableSet (S36.measurableSet_E4 hD z r a K)
  have hca := LQGMetric.UMeasurableSet.of_measurableSet
    (S36.measurableSet_exists_circleAverage r z)
  have heq : SourceEvent D ξ Q z r q a K θ k =
      {g : DistC | ∃ c : ℝ, IsCircleAverage g r z c} ∩
      {g : DistC | S36Events.EventClause1 (D g) z r q θ} ∩
      {g : DistC | ∀ c : ℝ, IsCircleAverage g r z c →
        S36.E2Prop (D g) ξ Q z r q a θ (2 * k) 1 c} ∩
      {g : DistC | S36Events.EventClause3 (D g) z r q a} ∩
      {g : DistC | S36.E4Prop (D g) z r a K} := by
    ext g
    constructor
    · rintro ⟨c, hc, h1', h2', h3', h4'⟩
      refine ⟨⟨⟨⟨⟨c, hc⟩, h1'⟩, ?_⟩, h3'⟩, h4'⟩
      intro c' hc'
      rw [← isCircleAverage_unique hc hc']
      exact h2'
    · rintro ⟨⟨⟨⟨⟨c, hc⟩, h1'⟩, h2'⟩, h3'⟩, h4'⟩
      exact ⟨c, hc, h1', h2' c hc, h3', h4'⟩
  rw [heq]
  exact (((hca.inter h1).inter h2).inter h3).inter h4


end SupercriticalConformalCovariance.GoodAnnulus

namespace SupercriticalConformalCovariance.GoodAnnulus
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

/-- Choose the small parameter in the paper's dyadic family. -/
theorem exists_dyadic_q_small (q₁ X θ : ℝ) (hq₁ : 0 < q₁) (hθ : 0 < θ) :
    ∃ (n : ℕ) (q : Ioo (0 : ℝ) (1 / 100)),
      (q : ℝ) = (1 / 2 : ℝ) ^ n ∧ (q : ℝ) ≤ q₁ ∧ X ≤ (q : ℝ) ^ (-θ) := by
  obtain ⟨q₀, hq₁', hX⟩ := exists_q_small q₁ X θ hq₁ hθ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one q₀.2.1
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hpos : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) _
  let q : Ioo (0 : ℝ) (1 / 100) :=
    ⟨(1 / 2 : ℝ) ^ n, hpos, hn.trans q₀.2.2⟩
  refine ⟨n, q, rfl, hn.le.trans hq₁', ?_⟩
  exact hX.trans (Real.rpow_le_rpow_of_nonpos hpos hn.le (by linarith))


end SupercriticalConformalCovariance.GoodAnnulus
