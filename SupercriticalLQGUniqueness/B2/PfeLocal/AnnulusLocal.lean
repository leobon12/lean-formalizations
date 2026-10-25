import SupercriticalLQGUniqueness.B2.PfeLocal.AnnulusEvent
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality
import LQGMetric.Blueprint.M2Defs

 






set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Metric

 
def eventCarrier (z : ℂ) (r : Set.Ioi (0 : ℝ)) : Set ℂ :=
  {u | (r : ℝ) / 2 < ‖u - z‖ ∧ ‖u - z‖ < 2 * (r : ℝ)}

 


theorem eventCarrier_eq_lm_annulus (z : ℂ) (r : Set.Ioi (0 : ℝ)) :
    eventCarrier z r =
      (LQGMetric.Blueprint.annulus z ((1 / 8 : ℝ) * (4 * (r : ℝ)))
        ((1 / 2 : ℝ) * (4 * (r : ℝ))) : Set ℂ) := by
  ext u
  change ((r : ℝ) / 2 < ‖u - z‖ ∧ ‖u - z‖ < 2 * (r : ℝ)) ↔
    (1 / 8 : ℝ) * (4 * (r : ℝ)) < ‖u - z‖ ∧
      ‖u - z‖ < (1 / 2 : ℝ) * (4 * (r : ℝ))
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

 





theorem annulus_costs_eq_of_internal_eq (D E : LSCMetric)
    (hBD : Uniqueness.BiLipschitz.Barrier.Barrier D)
    (hBE : Uniqueness.BiLipschitz.Barrier.Barrier E)
    (hLD : D.IsLengthSpace) (hLE : E.IsLengthSpace)
    (z : ℂ) (r : Set.Ioi (0 : ℝ))
    (hint : D.internal (eventCarrier z r) = E.internal (eventCarrier z r)) :
    acrossDist D (innerAnnulus z r r.2) = acrossDist E (innerAnnulus z r r.2) ∧
      aroundDist D (outerAnnulus z r r.2) = aroundDist E (outerAnnulus z r r.2) := by
  constructor
  · apply Uniqueness.BiLipschitz.Barrier.acrossDist_eq_of_internal_eq D E
      hBD hBE hLD hLE (innerAnnulus z r r.2) (R := 2 * (r : ℝ))
      (by
        change (r : ℝ) < 2 * (r : ℝ)
        have hr : 0 < (r : ℝ) := r.2
        linarith)
    simpa only [eventCarrier, innerAnnulus, EuclideanAnnulus.innerRadius,
      EuclideanAnnulus.center] using hint
  · apply Uniqueness.BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq
      D E (eventCarrier z r) hint (outerAnnulus z r r.2)
    intro u hu
    change u ∈ Metric.ball z (2 * (r : ℝ)) \
      closure (Metric.ball z (r : ℝ)) at hu
    rw [closure_ball z (ne_of_gt r.2)] at hu
    simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le,
      dist_eq_norm] at hu
    exact ⟨by linarith [hu.2, r.2], hu.1⟩

 


theorem mem_annulusEvent_iff_of_internal_eq {Ω : Type*} [MeasurableSpace Ω]
    (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (h : Ω → LQGMetric.DistC) (D E : Ω → LSCMetric)
    (ω ω' : Ω) (z : ℂ) (r : Set.Ioi (0 : ℝ)) (C : Set.Ioi (1 : ℝ))
    (hBD : Uniqueness.BiLipschitz.Barrier.Barrier (D ω))
    (hBE : Uniqueness.BiLipschitz.Barrier.Barrier (E ω'))
    (hLD : (D ω).IsLengthSpace) (hLE : (E ω').IsLengthSpace)
    (hcircle : LQGMetric.circleAvg (h ω) r z = LQGMetric.circleAvg (h ω') r z)
    (hint : (D ω).internal (eventCarrier z r) = (E ω').internal (eventCarrier z r)) :
    ω ∈ annulusEvent ξ c h D z r C ↔
      ω' ∈ annulusEvent ξ c h E z r C := by
  obtain ⟨hacross, haround⟩ :=
    annulus_costs_eq_of_internal_eq (D ω) (E ω') hBD hBE hLD hLE z r hint
  simp only [annulusEvent, Set.mem_ofPred_eq, hacross, haround, hcircle]

end SupercriticalLQGUniqueness.B2.PfeLocal
