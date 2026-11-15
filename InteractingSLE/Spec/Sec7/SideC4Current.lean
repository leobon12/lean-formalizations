/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC3Records
import InteractingSLE.Spec.Sec7.SideLCGerm
import InteractingSLE.Spec.Sec7.PocketSideInTailActual

/-!
# Actual charts for capacity-time current sets and original-time references

PROVE-SIDE-COLLAR2 continuation. Ready supplies the inherited analytic lift
at an arbitrary live relative capacity, not just at an original visit.
At an original visit the old chart has exactly the complement of the filled
capacity reference as its domain. An earlier ambient hull gives nesting.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketUnionPt Sec7.Lemma71C

variable {Ω : Type} [MeasurableSpace Ω] {j : SideTest Ω} {i : BothLow}
  {d : WordObjects Ω}

/-- The native chart at any live relative capacity carries an analytic
derivative logarithm with exactly its inherited lift. -/
theorem isDomainChart_relChart_of_ready (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) :
    IsDomainChart (H \ activeCompl (j.target i d).event (j.target i d).curve
      (j.target i d).baseChart q ω)
      (relChart (j.target i d).baseChart (j.target i d).curve q ω) := by
  have hbase := isDomainChart_baseChart hj hRc hLc hω
  have hDriven := isDrivenCurve_target (i := i) hj ω hω
  obtain ⟨W, hW, hW0, -, -, -, heq⟩ :=
    exists_relChart_eq_loewner (c := (j.target i d).baseChart) hDriven hq
  have hcurrent := hbase.trans (isDomainChart_loewner hW hW0 q.coe_nonneg)
  rw [← Chart.loewner_eq_trans, ← heq] at hcurrent
  have hdom := (H_diff_activeCompl_eq_relChart_dom hω hq hDriven hbase.1).trans
    hcurrent.coe_dom
  exact hdom ▸ hcurrent

/-- On the initial event the reference complement is the literal physical
pocket cut by the regularized original hull. -/
theorem compl_capacityReference {ω : Ω} (hω : ω ∈ (j.target i d).event) (s : ℝ≥0) :
    H \ j.capacityReference i d s ω = (j.target i d).domain ω ∩
      (H \ regHull d.driver d.lifetime s ω) := by
  have hEvent : ω ∈ j.event := by rwa [target_event] at hω
  rw [capacityReference, eventFilled, ite_eq_left hEvent]
  ext z
  simp only [extHullSet, Set.mem_sdiff, mem_inter_iff, mem_union, mem_compl_iff]
  tauto

/-- At an actual original visit, the reference chart is a chart of the
exact reference complement, with its inherited logarithm. The equality of
regularized and original hulls is supplied simultaneously at all times by
`ae_regHull_eq` under the original coupling and infinite lifetime. -/
theorem isDomainChart_capacityReference_at_visit (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) (s : ℝ≥0)
    (hVisit : d.curve ω s ∈ (j.target i d).domain ω)
    (hHull : regHull d.driver d.lifetime s ω =
      QuantumZipper.fwdHull (fun t : ℝ => d.driver t.toNNReal ω) s) :
    IsDomainChart (H \ j.capacityReference i d s ω)
      (j.referenceVisitChart i d ω s) := by
  rw [compl_capacityReference hω s, hHull]
  exact isDomainChart_relChart_visitCapacity hj hRc hLc hω s.coe_nonneg hVisit

/-- An earlier original hull makes the actual current domain a subdomain
of the original-time reference chart. No physical collar equality follows
from this nesting assertion. -/
theorem current_dom_subset_reference_at_visit (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {q s : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω))
    (hVisit : d.curve ω s ∈ (j.target i d).domain ω)
    (hHull : regHull d.driver d.lifetime s ω =
      QuantumZipper.fwdHull (fun t : ℝ => d.driver t.toNNReal ω) s)
    (hSub : regHull d.driver d.lifetime s ω ⊆ j.hull d q ω) :
    ((relChart (j.target i d).baseChart (j.target i d).curve q ω).dom : Set ℂ) ⊆
      (j.referenceVisitChart i d ω s).dom := by
  have hOld := isDomainChart_capacityReference_at_visit hj hRc hLc hω s hVisit hHull
  have hbase := isDomainChart_baseChart hj hRc hLc hω
  rw [← activeDom_eq_relChart_dom hω hq (isDrivenCurve_target hj ω hω) hbase.1,
    activeDom_eq hj hRc hLc q ω hω hq, hOld.coe_dom, compl_capacityReference hω s]
  exact fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2 (hSub h)⟩

end InteractingSLE.Wire.Current.SideTest
