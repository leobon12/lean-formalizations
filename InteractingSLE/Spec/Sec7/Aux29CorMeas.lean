/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux29CorChart
import InteractingSLE.Spec.Sec7.PhaseContMeas
import InteractingSLE.Spec.Sec7.PocketTraversalMeasRand
import InteractingSLE.Spec.Sec7.PocketSideInInstGerm
import InteractingSLE.Spec.Sec7.Lemma725RefMarksWord

/-!
# Hitting measurability of a late side target's active complement

PROVE-AUX29-CORNER. `late_sideLimits_offExc` takes the hitting measurability of the current active
complement `activeCompl target.event target.curve target.baseChart q` (`hKm`). This file derives it for
every `Ready` late side test from the measurability of the walls and of the counterflow in `ω`
(`SideTest.measurable_activeCompl_of_ready`), through PROVE-PHASECONT's
`PhaseCont.measurable_activeCompl_locPrefixSigma` and `PocketUnionPt.locPrefixSigma_le`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopField Sec7.PocketJordan Sec7.PocketCoord Sec7.PocketWordAssembly
  Sec7.PocketTraversal Sec7.PocketStop Sec7.PocketWordPerQ Sec7.PocketSeedOpen Sec7.PocketUnionPt
  Sec7.PocketMarks Sec7.PocketCoupling

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}

/-- On the event, the base chart is a conformal chart of the pocket with forward map the coordinate. -/
theorem baseChart_dom_facts (hj : j.Ready d) :
    ∀ ω ∈ (j.target i d).event, ((j.target i d).baseChart ω).IsConformal ∧
      (((j.target i d).baseChart ω).dom : Set ℂ) = (j.target i d).domain ω ∧
      EqOn ((j.target i d).baseChart ω).1 ((j.target i d).chart ω) ((j.target i d).domain ω) := by
  intro ω hω
  have hprops := pChart_props (isOpen_domain (i := i) hj) (domain_subset_H_of_ready (i := i) hj)
    (isConformalBijection_chart_of_ready (i := i) hj) ω
  refine ⟨hprops.2.2.1, ?_, fun z _ => ?_⟩
  · change ((pChart (j.target i d).event (j.target i d).domain (j.target i d).chart ω).dom : Set ℂ) = _
    rw [hprops.2.2.2]
    ext z
    simp only [mem_ofPred_eq, hω, true_and, not_true_eq_false, false_and, or_false]
  · change pFwd (j.target i d).event (j.target i d).chart ω z = _
    rw [pFwd_of_mem hω]

/-- **Hitting measurability of the active complement** of a `Ready` late side test at every relative
capacity, from the measurability of the walls and of the counterflow. -/
theorem measurable_activeCompl_of_ready (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ t, Measurable fun ω => d.leftWall j.seed ω t)
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => d.curve ω u) (q : ℝ≥0) :
    Measurable[mΩ, hittingSigma]
      (activeCompl (j.target i d).event (j.target i d).curve (j.target i d).baseChart q) := by
  have h𝓦 : wallsSigma d.measure d.rightWall (d.leftWall j.seed) ≤ mΩ := wallsSigma_le hRm hLm
  have hRm' := measurable_right_wallsSigma (P := d.measure) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := d.measure) hRc hLc
  have hγ := isDrivenCurve_target (i := i) hj
  have hCo := isOpen_domain (i := i) hj
  have hCH := domain_subset_H_of_ready (i := i) hj
  have hψ := isConformalBijection_chart_of_ready (i := i) hj
  have hc := baseChart_dom_facts (i := i) hj
  have hCm := measurableSet_domain (i := i) hj hRc hLc
  rw [target_walls] at hCm
  have hready := hj
  rcases hready with ⟨-, hGm, -, hG, -, hcfg, hcfgI, hAm, hAG, -, hJ, hJm, -⟩
  have hGp := (measurableSet_rightLo_pos_and
    (mΩ := wallsSigma d.measure d.rightWall (d.leftWall j.seed)) hRm' hLm' hGm (fun ω hω => (hG ω
      hω).1)).1
  have hG0 : MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall j.seed)]
      {ω | ω ∈ j.outerEvent ∧ ¬ 0 < rightLo (d.rightWall ω) (d.leftWall j.seed ω)
        (StripSys.rt j.seed)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hA : MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall j.seed)] (j.target i d).event := by
    rw [target_event]
    exact hAm
  have hgoal : activeCompl (j.target i d).event (j.target i d).curve (j.target i d).baseChart q =
      activeCompl j.event (if j.infinite then
          travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart
        else travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (pChart j.event (fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
          j.chart) q := by
    simp only [SideTarget.baseChart, target_event, target_curve, target_domain, target_chart]
  rw [hgoal]
  simp only [SideTarget.baseChart, target_event, target_curve, target_domain, target_chart]
    at hγ hCo hCH hψ hc hCm hA
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hγ hAG hJ hJm ⊢
    have hγm : ∀ u, 0 ≤ u → Measurable fun ω : j.event =>
        travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω u := fun u hu =>
      PocketTraversalMeasRand.traversalMeasStatement_of_measurable h𝓦 hRm' hLm' hGp
        (fun ω hω => hcfg ω hω.1 hω.2) hηm j.event (h𝓦 _ hAm) hAG j.chart hJ hJm u hu
    have hψm : ∀ z, Measurable[wallsSigma d.measure d.rightWall (d.leftWall j.seed)]
        ({ω | ω ∈ j.event ∧ z ∈ cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)}.indicator
          fun ω => j.chart ω z) := fun z =>
      hJm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
        ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1).1).1.cfPt_openPt_notMem (h ▸ hω.2)⟩
    have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
        MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall j.seed)]
          {ω | ω ∈ j.event ∧ U ⊆ cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)} :=
      fun U hUo hUH => Lemma725RefMarks.measurableSet_subset_cfPocket hRm' hLm' hGp
        (fun ω hω => (hG ω hω.1).1) hAm hAG hUo hUH
    exact (PhaseCont.measurable_activeCompl_locPrefixSigma h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin hc q).mono
      (locPrefixSigma_le h𝓦 hA hγ hγm q) le_rfl
  · simp only [hI, ↓reduceIte] at hγ hAG hJ hJm ⊢
    have hcfgI' : ∀ ω ∈ {ω | ω ∈ j.outerEvent ∧ ¬ 0 < rightLo (d.rightWall ω) (d.leftWall j.seed ω)
        (StripSys.rt j.seed)}, IsCfPocketConfigInf (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)
          (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) := fun ω hω =>
      hcfgI ω hω.1 (le_antisymm (le_of_not_gt hω.2) (hG ω hω.1).1.changeCorner_props.1.1)
    have hγm : ∀ u, 0 ≤ u → Measurable fun ω : j.event =>
        travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω u := fun u hu =>
      measurable_travSubInf h𝓦 hRm' hLm' hG0 hcfgI' hηm hAG hJ hJm hu
    have hψm : ∀ z, Measurable[wallsSigma d.measure d.rightWall (d.leftWall j.seed)]
        ({ω | ω ∈ j.event ∧ z ∈ cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)}.indicator
          fun ω => j.chart ω z) := fun z =>
      hJm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
    have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
        MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall j.seed)]
          {ω | ω ∈ j.event ∧ U ⊆ cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)} :=
      fun U hUo hUH => Lemma725RefMarks.measurableSet_subset_cfPocket hRm' hLm' hG0
        (fun ω hω => (hG ω hω.1).1) hAm hAG hUo hUH
    exact (PhaseCont.measurable_activeCompl_locPrefixSigma h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin hc q).mono
      (locPrefixSigma_le h𝓦 hA hγ hγm q) le_rfl

end InteractingSLE.Wire.Current.SideTest
