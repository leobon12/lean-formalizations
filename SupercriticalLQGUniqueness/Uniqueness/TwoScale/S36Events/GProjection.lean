import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.Projection
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3




set_option autoImplicit false
noncomputable section
open Set
open LQGMetric (DistC)
namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events

 

theorem G_iff_GWitness (D E : LSCMetric)
    (r κ C : Set.Ioi (0 : ℝ)) :
    OptimalConstants.Ratios.G D E r κ C ↔
      ∃ z w : ℂ, Toolkit.MovingEndpoints.GWitness r κ C ((D, E), (z, w)) := by
  simp only [OptimalConstants.Ratios.G, Toolkit.MovingEndpoints.GWitness, Toolkit.MovingEndpoints.movingOpenSetDist,
    ← OptimalConstants.Ratios.setDist_eq_iInf_prod, OptimalConstants.Ratios.ratioPair_iff_finite_positive]
  simp only [and_assoc]

 
theorem GEvent_um (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E)
    (r κ C : Set.Ioi (0 : ℝ)) :
    LQGMetric.UMeasurableSet (OptimalConstants.Ratios.GEvent D E r κ C) := by
  have h := Toolkit.MovingEndpoints.GWitnessEvent_um D E hD hE r κ C
  have heq : OptimalConstants.Ratios.GEvent D E r κ C =
      {g : DistC | ∃ z w : ℂ, Toolkit.MovingEndpoints.GWitness r κ C ((D g, E g), (z, w))} := by
    ext g
    exact G_iff_GWitness (D g) (E g) r κ C
  exact heq ▸ h

 
theorem Gtilde_iff_GtildeWitness (D E : LSCMetric)
    (r κ C : Set.Ioi (0 : ℝ)) :
    OptimalConstants.Ratios.Gtilde D E r κ C ↔
      ∃ z w : ℂ, Toolkit.MovingEndpoints.GtildeWitness r κ C ((D, E), (z, w)) := by
  simp only [OptimalConstants.Ratios.Gtilde, Toolkit.MovingEndpoints.GtildeWitness, Toolkit.MovingEndpoints.movingOpenSetDist,
    ← OptimalConstants.Ratios.setDist_eq_iInf_prod, OptimalConstants.Ratios.ratioPair_iff_finite_positive]
  simp only [and_assoc]

theorem GtildeEvent_um (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E)
    (r κ C : Set.Ioi (0 : ℝ)) :
    LQGMetric.UMeasurableSet (OptimalConstants.Ratios.GtildeEvent D E r κ C) := by
  have h := Toolkit.MovingEndpoints.GtildeWitnessEvent_um D E hD hE r κ C
  have heq : OptimalConstants.Ratios.GtildeEvent D E r κ C =
      {g : DistC | ∃ z w : ℂ, Toolkit.MovingEndpoints.GtildeWitness r κ C ((D g, E g), (z, w))} := by
    ext g
    exact Gtilde_iff_GtildeWitness (D g) (E g) r κ C
  exact heq ▸ h

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events
