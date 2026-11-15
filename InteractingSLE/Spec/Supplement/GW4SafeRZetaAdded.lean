/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaRead
import InteractingSLE.Spec.Supplement.GW4SafeREpsilonRef
import InteractingSLE.Spec.Supplement.GW4SafeRClipSet
import InteractingSLE.Spec.Sec7.R5EnlAdded

/-!
# GW4: the actual added set is retained by the later physical record

This discharges the added-set measurability input of the conditioned
increment-law theorem for the literal component line references. The
reference event is its actual live event; the canonical safe hull is used
at the later line, including outcomes where that line has stopped.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar Supp8.RelSafe LocalSets Sec7.R5Enl Sec7.PocketStopSide

/-- The actual reference live event belongs to its physical past. -/
theorem measurableSet_componentLine_live {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} {F : Frame} (hF : F.IsOk)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V) (t : ℝ≥0) :
    MeasurableSet[physFilt Frame.measurable_gw4Rec hWm ν t]
      {ω | lineClock F Wd GT V t ω < V ω} := by
  have h := Frame.measurableSet_lineSafe hF hGT hWm hGTm hGTae hver isClosed_empty t
  simpa only [empty_disjoint, and_true] using h

/-- For actual line references, the added set of the event-conditioned
charts is hitting-measurable in the later physical record. -/
theorem measurable_componentLine_addedSet {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} {F : Frame} (hF : F.IsOk)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V) {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[physFilt Frame.measurable_gw4Rec hWm ν t, hittingSigma]
      (globalOldChartAddedSet
        (oldOn {ω | lineClock F Wd GT V s ω < V ω} (componentLineChart F Wd GT R V s))
        (curOn {ω | lineClock F Wd GT V s ω < V ω}
          (fun ω => H \ safeHull F Wd GT R V t ω))) := by
  have hG := measurableSet_componentLine_live hF hGT hWm hGTm hGTae hver s
  have hOld : ∀ ω ∈ {ω | lineClock F Wd GT V s ω < V ω},
      (componentLineChart F Wd GT R V s ω).IsConformal := by
    intro ω _
    have hW : Continuous (wpath R ω) := (hver.1.1.2.1 ω).comp continuous_real_toNNReal
    have hW0 : wpath R ω 0 = 0 := by
      simpa only [wpath, Real.toNNReal_zero] using hver.1.1.2.2.1 ω
    exact Chart.isConformal_id.loewner hW hW0
      (lineClock F Wd GT V s ω).toNNReal.coe_nonneg
  have hDom : ∀ ω ∈ {ω | lineClock F Wd GT V s ω < V ω},
      ((componentLineChart F Wd GT R V s ω).dom : Set ℂ) =
        H \ safeHull F Wd GT R V s ω := by
    intro ω hω
    exact (componentLineChart_domain (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)).trans
      (H_diff_safeHull_of_lt F Wd GT R V s ω hω).symm
  exact measurable_globalOldChartAddedSet_oldOn
    ((physFilt Frame.measurable_gw4Rec hWm ν).mono hst) hG hOld
    (measurable_componentLineChart_indicator hF hGT hWm hGTm hGTae hver s hG)
    (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver s) hDom
    (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver t)
    (fun ω _ => Frame.isOpen_H_diff_safeHull hver t ω)

end InteractingSLE.Theorem14.GW4Fix
