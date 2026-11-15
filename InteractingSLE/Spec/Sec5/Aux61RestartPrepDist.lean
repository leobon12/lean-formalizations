import InteractingSLE.Spec.Sec5.Aux61RestartPrepPath

/-!
# Measurable tip clearance from the retained counterflow hull

Packet PROVE-AUX61-R1. Reuse the hitting-sigma-algebra distance reader and
the existing Caratheodory theorem. The distance is measured at the actual
random tip, including the empty-hull case of real-valued infDist.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49 LocalSets

/-- The physical counterflow hull read from the stopped record lies in H. -/
theorem historyHull_subset_H {Ω : Type*} (s : ℝ≥0) (Y : Ω → HistorySpace 0 0) (ω : Ω) :
    historyHull s Y ω ⊆ H := by
  rintro _ ⟨z, hz, rfl⟩
  exact negInv_mem_H hz.1

/-- The actual unbounded physical hull is hitting-measurable from the
retained stopped record. No compact-hull hypothesis is imposed. -/
theorem measurable_historyHull
    {Ω : Type*} [MeasurableSpace Ω] {s : ℝ≥0} {Y : Ω → HistorySpace 0 0}
    (hY : Measurable fun ω => cfStop s (Y ω)) :
    Measurable[_, hittingSigma] (historyHull s Y) := by
  have hDom : ∀ c ρ, MeasurableSet {ω | closedBall c ρ ⊆ H \ historyHull s Y ω} := by
    intro c ρ
    have h := measurableSet_comp_of_stopSigma
      (measurableSet_closedBall_subset_dom_cfChart (s := s) c ρ) hY
    simpa only [preimage_ofPred_eq, coe_dom_cfChart, historyHull] using h
  have h := measurable_complementH_of_closedBall hDom
  convert h using 1
  funext ω
  ext z
  constructor
  · intro hz
    exact ⟨historyHull_subset_H s Y ω hz, fun h => h.2 hz⟩
  · intro hz
    by_contra hzK
    exact hz.2 ⟨hz.1, hzK⟩

/-- Distance to a hitting-measurable H-set, evaluated at a measurable random
point. The real-valued empty-set convention is preserved literally. -/
theorem measurable_infDist_random_point
    {Ω : Type*} [MeasurableSpace Ω] {A : Ω → Set ℂ}
    (hA : Measurable[_, hittingSigma] A) {z : Ω → ℂ} (hz : Measurable z) :
    Measurable fun ω => infDist (z ω) (A ω ∩ H) := by
  let f : ℂ → Ω → ℝ := fun x ω => infDist x (A ω ∩ H)
  have hm : ∀ x : ℂ, Measurable (f x) := by
    intro x
    change Measurable fun ω => (infEDist x (A ω ∩ H)).toReal
    exact ((measurable_infEDist_inter_H x).comp hA).ennreal_toReal
  have hc : ∀ ω, Continuous fun x => f x ω := fun ω => continuous_infDist_pt _
  have h : Measurable (Function.uncurry f) :=
    measurable_uncurry_of_continuous_of_measurable (u := f) hc hm
  have hpair : Measurable (fun ω : Ω => (z ω, ω)) := hz.prodMk measurable_id
  have hcomp := h.comp hpair
  exact hcomp

/-- Positive clearance of the current random tip from the actual retained
hull is a measurable event of the stopped observations. -/
theorem measurable_infDist_historyHull
    {Ω : Type*} [MeasurableSpace Ω] {s : ℝ≥0} {Y : Ω → HistorySpace 0 0}
    (hY : Measurable fun ω => cfStop s (Y ω)) {z : Ω → ℂ} (hz : Measurable z) :
    Measurable fun ω => infDist (z ω) (historyHull s Y ω) := by
  have h := measurable_infDist_random_point (measurable_historyHull hY) hz
  have heq : ∀ ω, historyHull s Y ω ∩ H = historyHull s Y ω :=
    fun ω => inter_eq_left.mpr (historyHull_subset_H s Y ω)
  simpa only [heq] using h

end InteractingSLE.Sec5.Aux61Restart
