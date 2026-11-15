/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSyncClock
import InteractingSLE.Spec.Sec7.PocketSideInInstGerm

/-!
# Actual SideTest domains at a common original visit

PROVE-POCKET-SIDEIN. The relative capacity is constructed for both actual
pocket shapes. At a visit its ambient stop is the original time, so its
current domain is cut by the original ambient hull. This is deterministic;
it does not substitute a random relative time into an almost-sure law.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec6 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketWordAssembly
  Sec7.PocketSeedOpen Sec7.PocketMarks Sec7.PocketCoupling Sec7.PocketWordPerQ
  Sec7.PocketStopField Sec7.PocketStopSide Sec7.PocketUnionPt Sec7.Lemma71C
  Sec7.PocketStopMarked Sec7.PocketTraversal Sec7.PocketStop

variable {Ω : Type} [MeasurableSpace Ω]

/-- The actual relative capacity reached at an original time, for the
selected bounded or seed-opening pocket. -/
def visitCapacity (j : SideTest Ω) (d : WordObjects Ω) (ω : Ω) (t : ℝ) : ℝ :=
  if j.infinite then
    relCapInf (d.curve ω) (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
      (firstHit (d.curve ω) (cfArcRInf (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0))
      (j.chart ω) t
  else
    relCap (d.curve ω) (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
      (firstHit (d.curve ω) (cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 1))
      (firstHit (d.curve ω) (cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0))
      (j.chart ω) t

/-- At an actual original visit the constructed relative capacity is
positive and live, and its right-stop hull is the original ambient hull. -/
theorem visitCapacity_spec {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) :
    0 < j.visitCapacity d ω t ∧
      ((j.visitCapacity d ω t).toNNReal : ℝ≥0∞) < capLife ((j.target i d).curve ω) ∧
      j.hull d (j.visitCapacity d ω t).toNNReal ω =
        QuantumZipper.fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t := by
  rw [target_event] at hω
  rw [target_domain] at hvisit
  rcases hj with ⟨-, -, -, hG, -, hcfg, hcfgI, -, hAG, -, hJ, -⟩
  rw [target_curve]
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte, visitCapacity] at hAG hJ ⊢
    have hc := hcfg ω (hAG hω).1 (hAG hω).2
    have hP := hc.conf.isReversePocket_of_counterflow
      (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
      hc.trace hc.continuous_W hc.W_zero hc.revR hc.revL hc.visR
    have hψ : Sec6.IsJordanCoord
        (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
        (cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0)
        (cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 1) (j.chart ω) := by
      rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
      exact hJ ω hω
    have hv := hP.mem_visitSet ht hvisit
    obtain ⟨hpos, hlive⟩ := relCap_pos_lt_of_visit hP hc.attach hψ hv
    refine ⟨hpos, ?_, ?_⟩
    · rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hpos.le]
      exact hlive
    · simp only [hull, hI, Bool.false_eq_true, ↓reduceIte, stopHull]
      rw [Real.coe_toNNReal _ hpos.le, ambTime_relCap_of_visit hP hc.attach hψ hv]
  · simp only [hI, ↓reduceIte, visitCapacity] at hAG hJ ⊢
    have hzero := le_antisymm (le_of_not_gt (hAG hω).2)
      (hG ω (hAG hω).1).1.changeCorner_props.1.1
    have hc := hcfgI ω (hAG hω).1 hzero
    have hψ : Sec6.IsJordanCoordInf
        (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
        (cfArcRInf (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0) (j.chart ω) := by
      rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
      exact hJ ω hω
    have hv := hc.isReversePocketInf.mem_visitSet ht hvisit
    obtain ⟨hpos, hlive⟩ := relCapInf_pos_lt_of_visit hc.isReversePocketInf hc.attach hψ hv
    refine ⟨hpos, ?_, ?_⟩
    · rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hpos.le]
      exact hlive
    · simp only [hull, hI, ↓reduceIte, stopHullInf]
      rw [Real.coe_toNNReal _ hpos.le,
        ambTimeInf_relCapInf_of_visit hc.isReversePocketInf hc.attach hψ hv]

/-- The actual active domain at the capacity of an interior original visit
is cut by that original-time ambient hull. -/
theorem activeDom_visitCapacity {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) :
    activeDom (j.target i d).event (j.target i d).curve (j.target i d).baseChart
      (j.visitCapacity d ω t).toNNReal ω =
        (j.target i d).domain ω ∩
          (H \ QuantumZipper.fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t) := by
  obtain ⟨-, hlive, hhull⟩ := visitCapacity_spec hj hω ht hvisit
  rw [activeDom_eq hj hRc hLc _ ω hω hlive, hhull]

/-- The current physical chart has the same original-time domain identity.
This supplies the common-hull premise for two current pocket charts. -/
theorem relChart_dom_visitCapacity {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) :
    ((relChart (j.target i d).baseChart (j.target i d).curve
      (j.visitCapacity d ω t).toNNReal ω).dom : Set ℂ) =
        (j.target i d).domain ω ∩
          (H \ QuantumZipper.fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t) := by
  have hchart := isPocketChartOn hj hRc hLc (i := i)
  obtain ⟨-, hlive, -⟩ := visitCapacity_spec hj hω ht hvisit
  rw [← activeDom_eq_relChart_dom hω hlive (isDrivenCurve_target hj ω hω) (hchart.1 ω hω).1]
  exact activeDom_visitCapacity hj hRc hLc hω ht hvisit

end InteractingSLE.Wire.Current.SideTest
