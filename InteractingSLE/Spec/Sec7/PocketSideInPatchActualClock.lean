/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInPatchClock

/-!
# The actual pocket capacity trace at a common original visit

PROVE-POCKET-SIDEIN. Ready identifies both pocket shapes with their erased
traversals. At an interior original visit the capacity trace is the actual
initial base chart applied to the original counterflow point.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec6 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketWordAssembly
  Sec7.PocketSeedOpen Sec7.PocketMarks Sec7.PocketCoupling Sec7.PocketStopSide
  Sec7.PocketTraversal Sec7.PocketStopMarked Sec7.Lemma71C

variable {Ω : Type} [MeasurableSpace Ω]

/-- The actual current capacity trace is the initial physical chart of the
counterflow point at the original visit. Both actual clocks are undone. -/
theorem capTrace_target_visitCapacity {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) :
    capTrace ((j.target i d).curve ω) (j.visitCapacity d ω t).toNNReal =
      ((j.target i d).baseChart ω).1 (d.curve ω t) := by
  have hc := (isPocketChartOn hj hRc hLc (i := i)).1 ω hω
  have hBase : ((j.target i d).baseChart ω).1 (d.curve ω t) = j.chart ω (d.curve ω t) := by
    simpa only [target_chart] using hc.2.2.1 hvisit
  rw [hBase, target_curve]
  rw [target_event] at hω
  rw [target_domain] at hvisit
  rcases hj with ⟨-, -, -, hG, -, hcfg, hcfgI, -, hAG, -, hJ, -⟩
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte, visitCapacity] at hAG hJ ⊢
    have hcfg := hcfg ω (hAG hω).1 (hAG hω).2
    have hP := hcfg.conf.isReversePocket_of_counterflow
      (zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)
      hcfg.trace hcfg.continuous_W hcfg.W_zero hcfg.revR hcfg.revL hcfg.visR
    have hψ : IsJordanCoord
        (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
        (cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0)
        (cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 1) (j.chart ω) := by
      rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
      exact hJ ω hω
    exact capTrace_relCap_of_visit hP hcfg.attach hψ (hP.mem_visitSet ht hvisit)
  · simp only [hI, ↓reduceIte, visitCapacity] at hAG hJ ⊢
    have hzero := le_antisymm (le_of_not_gt (hAG hω).2)
      (hG ω (hAG hω).1).1.changeCorner_props.1.1
    have hcfg := hcfgI ω (hAG hω).1 hzero
    have hψ : IsJordanCoordInf
        (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
        (cfArcRInf (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0) (j.chart ω) := by
      rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
      exact hJ ω hω
    exact capTrace_relCapInf_of_visit hcfg.isReversePocketInf hcfg.attach hψ
      (hcfg.isReversePocketInf.mem_visitSet ht hvisit)

end InteractingSLE.Wire.Current.SideTest
