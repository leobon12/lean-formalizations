/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R1CActual

/-! # The certified counterflow record reads its frozen driver

The existing state certificate identifies the regularized counterflow
driver at every record carrying it. No future trace is an input.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAB
open Aux61R1C GlueCond LawUnique Restart.FlowStopIdentG

/-- The stopped counterflow history's driver reader is the certified
record driver frozen at the retained time. -/
theorem histPath_cfStop_eq_frozenDrv {s : ℝ≥0} {y : HistorySpace 0 0}
    (hS : StateCert s y) : Sec4.histPath (cfStop s y) = frozenDrv s y := by
  funext t
  have hl := (continuous_fst.tendsto (histState y (min t s))).comp
    (hS.tendsto (min_le_right t s))
  have heq : (fun n => ((cfStop s y).2 (lowerDyadic (min t s) n)).1) =
      (fun n => (y.2 (lowerDyadic (min t s) n)).1) := by
    funext n
    rw [Sec4.stopHistory_snd_of_le
      (show dyadicTime (lowerDyadic (min t s) n) ≤ Aux50Hit.cstop s y from
        (dyadicTime_lowerDyadic_le _ _).trans (min_le_right _ _))]
  change (limUnder atTop fun n => ((cfStop s y).2
    (lowerDyadic (min t (Sec4.histStop (cfStop s y))) n)).1) = _
  rw [histStop_cfStop, heq]
  exact hl.limUnder_eq

/-- On the state-certified records, regularizing the stopped driver
does not change it. -/
theorem regPath_cfStop_eq_frozenDrv {s : ℝ≥0} {y : HistorySpace 0 0}
    (hS : StateCert s y) : Sec4.regPath (cfStop s y) = frozenDrv s y := by
  have hc : Continuous (Sec4.histPath (cfStop s y)) := by
    rw [histPath_cfStop_eq_frozenDrv hS]
    exact hS.continuous_frozenDrv
  exact (QuantumZipper.Thm18Asm.G1Pkg.pathReg_spec.2.2 _ hc).trans (histPath_cfStop_eq_frozenDrv hS)

/-- The reflected-hull record uses exactly the same centered driver
as the certified frozen-record trace construction. -/
theorem cfDrv0_eq_frozenDrv {s : ℝ≥0} {y : HistorySpace 0 0} (hS : StateCert s y) :
    CrossCond.Word49.cfDrv0 s y = Ito.rpath (frozenDrv s y) := by
  funext t
  simp only [CrossCond.Word49.cfDrv0, regPath_cfStop_eq_frozenDrv hS,
    Ito.rpath, Real.toNNReal_zero, hS.frozenDrv_zero, sub_zero]

end InteractingSLE.Sec5.Aux61SlitWAB
