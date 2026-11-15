/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC6Clock
import InteractingSLE.Spec.Sec7.PocketSideInCensusVersions

/-!
# The initial current set is the actual zero-time reference

PROVE-SIDE-COLLAR2. The equality is global, including the normalization
off the candidate event. It permits comparison of arbitrary versions of
the two local means without an increment law at zero capacity.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWallsFin Sec7.PocketStop
  Sec7.PocketTraversal Sec7.PocketCoupling Sec7.Lemma71C Sec7.PocketStopField
  Sec7.PocketUnionPt Sec7.PocketAdapt

variable {Ω : Type} [MeasurableSpace Ω]

/-- The canonical current filled set at zero capacity is exactly the
original zero-time reference, on all samples. -/
theorem activeCompl_zero_eq_capacityReference {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) :
    activeCompl (j.target i d).event (j.target i d).curve (j.target i d).baseChart 0 =
      j.capacityReference i d 0 := by
  rw [capacityReference, original_filling_zero]
  funext ω
  by_cases hω : ω ∈ (j.target i d).event
  · have hDriven := isDrivenCurve_target hj ω hω
    have hq := PocketPhaseMeans.capLife_pos hDriven
    obtain ⟨W, hW, -, q', hq', hWeq, -⟩ :=
      exists_relChart_eq_loewner (c := (j.target i d).baseChart) hDriven hq
    have hHull : QuantumZipper.fwdHull
        (fun s : ℝ => segDriver ((j.target i d).curve ω) s.toNNReal) 0 = ∅ :=
      (fwdHull_eq_of_eqOn (by rfl) hq' hWeq).trans
        (QuantumZipper.RS.fwdHull_zero_eq_empty hW)
    have hbase := isDomainChart_baseChart hj hRc hLc hω
    have hjω : ω ∈ j.event := by rwa [target_event] at hω
    rw [activeCompl, PocketCoupling.activeDom_eq hω hq, NNReal.coe_zero, hHull,
      sdiff_empty, hbase.2.1, eventFilled, ite_eq_left hjω]
    ext z
    simp only [extHullSet, Set.mem_sdiff, mem_union, mem_inter_iff, mem_compl_iff, notMem_empty,
      or_false]
  · have hjω : ω ∉ j.event := by rwa [target_event] at hω
    rw [activeCompl, activeDom_eq_empty (fun h => hω h.1), sdiff_empty,
      eventFilled, ite_eq_right hjω]

/-- Installing any family containing original zero gives an exact current
reference at that index; its zero-time lift is also the literal current lift. -/
theorem visit_reference_zero_eq {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (e : Late.SideData Ω) (s : ℕ → ℝ≥0) {r : ℕ} (hr : s r = 0) :
    let refs := e.withVisitReferences i j d hKilled s
    liveExt (j.target i d).event (j.target i d).curve (j.target i d).domain
      (refs.sets r) refs.level =
        activeCompl (j.target i d).event (j.target i d).curve (j.target i d).baseChart 0 ∧
      ∀ ω ∈ (j.target i d).event,
        refs.lift r ω = (relChart (j.target i d).baseChart (j.target i d).curve 0 ω).2.2 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [visit_references_liveExt hj hKilled e s r, hr,
      activeCompl_zero_eq_capacityReference hj hRc hLc]
  · intro ω hω
    change (j.referenceVisitChart i d ω (s r)).2.2 = _
    rw [hr, NNReal.coe_zero, referenceVisitChart_zero_lift hj hω]
    exact Theorem14.GW2aCont.loewner_zero_lift.symm

end InteractingSLE.Wire.Current.SideTest
