import SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour.MetricCurveTour
import SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour.PaidSum
import SupercriticalLQGUniqueness.Uniqueness.Objects.Network.EventNetworkLink




 


set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent
open LQGMetric.MetricGeometry

 

theorem linked_trace_reachability {C : Constants} {T : TubeData}
    (hData : DataMatch C T)
    (P : T.netSites → ℝ → ℂ) (t u : T.netSites → ℝ)
    (hContact : ∀ x y : T.netSites,
      T.netRadius < dist (x : ℂ) y →
      dist (x : ℂ) y < 2*T.netRadius →
      (((P x) '' Icc (t x) (u x)) ∩
        ((P y) '' Icc (t y) (u y))).Nonempty) :
    ∀ x y : T.netSites, Relation.ReflTransGen
      (fun x y => (((P x) '' Icc (t x) (u x)) ∩
        ((P y) '' Icc (t y) (u y))).Nonempty) x y := by
  have hM2 : ∀ x ∈ T.netSites, ∀ y ∈ T.netSites,
      Relation.ReflTransGen
        (fun v w : ℂ => v ∈ T.netSites ∧ w ∈ T.netSites ∧
          T.netRadius < dist v w ∧ dist v w < 2*T.netRadius) x y := by
    unfold DataMatch at hData
    tauto
  let R : ℂ → ℂ → Prop := fun v w => v ∈ T.netSites ∧ w ∈ T.netSites ∧
    T.netRadius < dist v w ∧ dist v w < 2*T.netRadius
  have hlift : ∀ {v w : ℂ}, Relation.ReflTransGen R v w →
      ∀ hv : v ∈ T.netSites, ∀ hw : w ∈ T.netSites,
      Relation.ReflTransGen
        (fun x y : T.netSites => (((P x) '' Icc (t x) (u x)) ∩
          ((P y) '' Icc (t y) (u y))).Nonempty)
        (⟨v,hv⟩ : T.netSites) (⟨w,hw⟩ : T.netSites) := by
    intro v w hvw
    induction hvw with
    | refl =>
        intro hv hw
        exact Relation.ReflTransGen.refl
    | @tail b c hbc hstep ih =>
        intro hv hc
        have hb : b ∈ T.netSites := hstep.1
        exact (ih hv hb).tail
          (hContact ⟨b,hb⟩ ⟨c,hc⟩ hstep.2.2.1 hstep.2.2.2)
  intro x y
  exact hlift (hM2 x x.property y y.property) x.property y.property


 

theorem event_network_tour {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g)
    (hU : tubeSet T ⊆ ball 0 (2.5*C.r))
    (hEucl : ∀ (P : ℝ → ℂ) (a b : ℝ),
      (D g).IsCurve P a b → ((D g).len P a b < ∞) →
        ContinuousOn P (Icc a b)) :
    ∃ (pi : ℝ → ℂ) (s t : ℝ), (D g).IsCurve pi s t ∧
      pi '' Icc s t ⊆ tubeSet T ∧
      LQGMetric.Disconnects (pi '' Icc s t)
        (sphere 0 C.r) (sphere 0 (3*C.r)) ∧
      (∀ y ∈ closure (tubeSet T),
        ∃ p ∈ pi '' Icc s t, dist y p < C.A_set*C.r) ∧
      (D g).len pi s t ≤
        ENNReal.ofReal C.A_internal * normalizer C g C.r 0 := by
  classical
  obtain ⟨P, t, u, hTr, hBarrier, hDense, hContact⟩ :=
    Objects.Network.event_linked_paid_traces h hU hEucl
  have hS : T.netSites.Nonempty := by unfold DataMatch at hData; tauto
  have hNonempty : Nonempty T.netSites := by
    obtain ⟨x,hx⟩ := hS
    exact ⟨⟨x,hx⟩⟩
  have hconn := linked_trace_reachability hData P t u hContact
  obtain ⟨pi,s,v,hCurve,hTrace,hLen⟩ :=
    finite_connected_metric_curves_tour (D g) P t u
      (fun x => (hTr x).1) hNonempty hconn
  refine ⟨pi,s,v,hCurve,?_,?_,?_,?_⟩
  · rw [hTrace]
    intro z hz
    obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hz
    exact (hTr x).2.2.1 hx
  · rw [hTrace]
    exact (Objects.Network.barrier_round_boundaries C.rPos hBarrier).1
  · simpa only [hTrace] using hDense
  · have : Nonempty T.netSites := hNonempty
    have hCard : (Finset.univ : Finset T.netSites).card = T.netSites.card := by simp
    have hPaidSub : ∀ x : T.netSites,
        (D g).len (P x) (t x) (u x) ≤
          ENNReal.ofReal (C.A_internal / (2*T.netSites.card)) *
            normalizer C g C.r 0 := fun x => (hTr x).2.2.2.2.le
    have hSum := double_paid_sum_le (Finset.univ : Finset T.netSites)
      C.A_internal (normalizer C g C.r 0) Finset.univ_nonempty
      (fun x => (D g).len (P x) (t x) (u x)) (by
        intro x _
        simpa only [hCard] using hPaidSub x)
    exact hLen.trans (by simpa only [hCard] using hSum)



end SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
