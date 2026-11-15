/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefPrefix
import InteractingSLE.Spec.Sec7.PocketSideInRetainActual

/-!
# The actual original-time reference record

PROVE-POCKET-SIDEIN. Retain the intended walls and the ambient driving
history through a fixed original time. The filled reference is measurable
for this record in both pocket shapes. Its relative normalization is zero.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ Sec7.PocketCoupling Sec7.PocketStop LocalSets WholeField

/-- The intended walls together with the original driving history through
the reference time. No current-relative time or later visit is an input. -/
@[instance_reducible] def originalReferenceInfo {Ω : Type} [mΩ : MeasurableSpace Ω] (j : SideTest Ω)
    (d : WordObjects Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime) (s : ℝ≥0) :
    MeasurableSpace Ω :=
  wallsSigma d.measure d.rightWall (d.leftWall j.seed) ⊔ drivingFiltration d.measure hKilled s

/-- The original reference record is an ambient sub-sigma-algebra. -/
theorem originalReferenceInfo_le {Ω : Type} [mΩ : MeasurableSpace Ω]
    {j : SideTest Ω} {d : WordObjects Ω}
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hMeas : ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t) (s : ℝ≥0) :
    j.originalReferenceInfo d hKilled s ≤ mΩ :=
  sup_le (wallsSigma_le (hMeas 0) (hMeas 1)) ((drivingFiltration d.measure hKilled).le s)

/-- The candidate event, the original hull and its pocket filling are all
recorded before applying any Gaussian/local-set law. -/
theorem original_reference_records {Ω : Type} [mΩ : MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hj : j.Ready d)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ k ω, Continuous (pairWallFamily j j d k ω)) (s : ℝ≥0) :
    MeasurableSet[j.originalReferenceInfo d hKilled s] (j.target i d).event ∧
      Measurable[j.originalReferenceInfo d hKilled s, hittingSigma]
        (fun ω => regHull d.driver d.lifetime s ω) ∧
      Measurable[j.originalReferenceInfo d hKilled s, hittingSigma]
        (eventFilled (j.target i d).event (j.target i d).domain
          (fun ω => regHull d.driver d.lifetime s ω)) := by
  let ℋ := j.originalReferenceInfo d hKilled s
  let ambient : MeasurableSpace Ω := mΩ
  have hWalls : (j.target i d).walls ≤ ℋ := by
    rw [target_walls]
    exact le_sup_left
  have hA : MeasurableSet[ℋ] (j.target i d).event := by
    apply hWalls
    rw [target_event, target_walls]
    obtain ⟨-, -, -, -, -, -, -, hEvent, -⟩ := hj
    exact hEvent
  have hF : Measurable[ℋ, hittingSigma] (fun ω => regHull d.driver d.lifetime s ω) := by
    have hτ : IsStoppingTime (drivingFiltration d.measure hKilled)
        (fun _ : Ω => (s : WithTop ℝ≥0)) :=
      isStoppingTime_const (drivingFiltration d.measure hKilled) s
    have hStop := measurable_regHull_stopping hCoupling
      (lt_trans (by norm_num) i.kappa_gt_four) hKilled hLife hτ (fun _ => WithTop.coe_ne_top)
    rw [IsStoppingTime.measurableSpace_const] at hStop
    have hFs : Measurable[drivingFiltration d.measure hKilled s, hittingSigma]
        (fun ω => regHull d.driver d.lifetime s ω) := by
      simpa only [WithTop.untopD_coe] using hStop
    exact hFs.mono le_sup_right le_rfl
  exact ⟨hA, hF, measurable_eventFilled_of_ready hj (hCont 0) (hCont 1) hWalls hA
    subset_rfl hF⟩

end InteractingSLE.Wire.Current.SideTest
