import SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour.NetworkTour
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces.Section4Interfaces
import LQGMetric.Field.CircleAvgGauss




 


set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 

theorem event_hasTubeSeparator {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g)
    (hU : tubeSet T ⊆ ball 0 (2.5*C.r))
    (hEucl : ∀ (P : ℝ → ℂ) (a b : ℝ),
      (D g).IsCurve P a b → ((D g).len P a b < ∞) →
        ContinuousOn P (Icc a b))
    (r : Set.Ioi (0:ℝ)) (hr : (r:ℝ) = C.r)
    (U : TopologicalSpace.Opens ℂ)
    (hTU : tubeSet T ⊆ (U : Set ℂ)) :
    EndSaving.Interfaces.HasTubeSeparator (D g) 0 r U
      (ENNReal.ofReal C.A_internal * normalizer C g C.r 0) := by
  obtain ⟨pi,s,t,hCurve,hTube,hSep,-,hLen⟩ :=
    event_network_tour h hU hEucl
  refine ⟨pi,s,t,hCurve,?_,?_,hLen⟩
  · intro v hv
    exact hTU (hTube ⟨v,hv,rfl⟩)
  · simpa only [hr] using hSep


 


theorem event_hasTubeSeparator_bounds_field {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g)
    (hU : tubeSet T ⊆ ball 0 (2.5*C.r))
    (hEucl : ∀ (P : ℝ → ℂ) (a b : ℝ),
      (D g).IsCurve P a b → ((D g).len P a b < ∞) →
        ContinuousOn P (Icc a b))
    {ξ : Set.Ioi (0:ℝ)} {Q : ℝ} {par : EndSaving.Interfaces.Parameters ξ}
    {r : Set.Ioi (0:ℝ)} (U : TopologicalSpace.Opens ℂ)
    (hTU : tubeSet T ⊆ (U : Set ℂ))
    (hXi : C.ξ = (ξ:ℝ)) (hQ : C.Q = Q) (hR : C.r = (r:ℝ))
    (hCt : par.Ctube = C.A_internal) {c : ℝ}
    (hc : IsCircleAverage g r 0 c) :
    EndSaving.Interfaces.HasTubeSeparator (D g) 0 r U
      (ENNReal.ofReal par.Ctube *
        ENNReal.ofReal ((r:ℝ) ^ ((ξ:ℝ)*Q) * Real.exp ((ξ:ℝ)*c))) := by
  have hAvg : LQGMetric.circleAvg g (r:ℝ) 0 = c :=
    LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hc
  have hN : normalizer C g C.r 0 =
      ENNReal.ofReal ((r:ℝ) ^ ((ξ:ℝ)*Q) * Real.exp ((ξ:ℝ)*c)) := by
    simp only [normalizer, hXi, hQ, hR, hAvg]
  simpa only [← hCt, hN] using
    event_hasTubeSeparator h hU hEucl r hR.symm U hTU


end SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
