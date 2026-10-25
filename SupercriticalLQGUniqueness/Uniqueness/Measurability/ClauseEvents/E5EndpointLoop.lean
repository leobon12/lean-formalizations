import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.EndpointLoopBorel
import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.E2ClauseBorel




 


set_option autoImplicit false
noncomputable section

open Set
open SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents

 

def e5A75 (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) : Ioo (3 / 4 : ℝ) 1 :=
  ⟨a, by
    have hq := q.2.2
    have ha := a.2.1
    exact ⟨by linarith, a.2.2⟩⟩

 

theorem endpointLoopAt_iff_ratioEndpointLoop (D : LSCMetric)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ))
    (u v x : ℂ) :
    TwoScale.S36Events.EndpointLoopAt D r a θ u v x ↔
      OptimalConstants.Ratios.EndpointLoop D r (e5A75 q a) θ u v x := by
  rfl

 

theorem endpointLoopAtFinite_measurable (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (θ : Ioi (0 : ℝ)) :
    MeasurableSet {p : LoopGeoInput | p.1 p.2.1 ≠ ⊤ ∧
      TwoScale.S36Events.EndpointLoopAt p.1 r a θ p.2.1.1 p.2.1.2 p.2.2} := by
  have h := endpointLoopFinite_measurable r (e5A75 q a) θ
  convert h using 1
  ext p
  simp only [Set.mem_ofPred_eq]
  exact and_congr Iff.rfl (endpointLoopAt_iff_ratioEndpointLoop p.1 r q a θ
    p.2.1.1 p.2.1.2 p.2.2)

end SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents
