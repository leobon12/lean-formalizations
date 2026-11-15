/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkDomRun
import InteractingSLE.Spec.Supplement.RelTransHull
import InteractingSLE.Spec.Supplement.Aux10FullLocal

/-!
# Aliveness at a launch is read from the filled closed trace

Packet PROVE-T14-SB2LIFT (round 7; the step after the run-chart domain identity, handoff §R6.2). A frozen launch
(`ExplState.launch` at the walk's horizon `⊤`) decides its status, its hits and its new records through the predicate
`lAlive c ⊤ D z`: the forward Loewner flow of the stopped driver, started at the chart point `c.1 z`, survives up to
the stop. For a regular piece with a finite lifetime `T` and a real chart point `y = c.1 z ≠ 0`:

* **`lAlive_iff_notMem_closure_fillH`**: `lAlive c ⊤ D z ↔ c.1 z ∉ closure (fill (α([0, T])))`, `α = trOf D` the
  chosen trace. The two directions are the library's real-point criteria
  (`Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol`, `Aux10.exists_isForwardSol_of_notMem_closure`). The hull
  of the stopped driver at the stop is the filled closed trace (`fwdHull_eq_fillH_horizon`, round 6);
* `lHit_iff`: a real chart point is hit at the stop iff it is alive before the stop and in the closure of the filled
  closed trace.

No exit classification of the piece (GW1's `ForwardExit`) is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

/-- **The hull of the stopped driver at the stop of a regular piece with a finite lifetime** is the filled closed
trace. -/
theorem fwdHull_stopDrv_eq {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular D.1 D.2) (hfin : D.2 ≠ ⊤) :
    fwdHull (stopDrv ⊤ D) (stopTime ⊤ D) = fillH (trOf D '' Icc 0 D.2.toNNReal) := by
  have hmin : min (⊤ : ℝ≥0∞) D.2 = D.2 := min_eq_right le_top
  set T : ℝ≥0 := D.2.toNNReal with hTdef
  have hT : ((T : ℝ≥0) : ℝ≥0∞) = D.2 := ENNReal.coe_toNNReal hfin
  set w : ℝ≥0 → ℝ := fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal with hwdef
  have hwc : Continuous w := CounterflowRange.continuous_stopped hP.2.1
  have hw0 : w 0 = 0 := by
    have := hP.continuous_stoppedReal.2
    simpa [hwdef] using this
  have hα := isGeneratingTrace_trOf hP
  have hαs : IsGeneratingTrace w (T : ℝ≥0∞) (trOf D) := by
    rw [hT]
    exact CounterflowRange.isGeneratingTrace_stopped hα
  have hh := fwdHull_eq_fillH_horizon hwc hw0 hαs
  have hdrv : stopDrv ⊤ D = fun s : ℝ => w s.toNNReal := by
    funext x
    simp only [stopDrv, retOf, hmin, hwdef]
  have htime : stopTime ⊤ D = (T : ℝ) := by
    simp only [stopTime, hmin, hTdef]
  rw [hdrv, htime, hh]

/-- **Aliveness at a launch of a regular piece with a finite lifetime**, at a real nonzero chart point. -/
theorem lAlive_iff_notMem_closure_fillH {c : Chart} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular D.1 D.2)
    (hfin : D.2 ≠ ⊤) {z : ℂ} (hre : (c.1 z).im = 0) (hne : c.1 z ≠ 0) :
    lAlive c ⊤ D z ↔ c.1 z ∉ closure (fillH (trOf D '' Icc 0 D.2.toNNReal)) := by
  have hmin : min (⊤ : ℝ≥0∞) D.2 = D.2 := min_eq_right le_top
  have hWc : Continuous (stopDrv ⊤ D) := by
    have h := hP.continuous_stoppedReal.1
    have e : stopDrv ⊤ D = fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal := by
      funext x
      simp only [stopDrv, retOf, hmin]
    rw [e]
    exact h
  have hW0 : stopDrv ⊤ D 0 = 0 := by
    have h := hP.continuous_stoppedReal.2
    simpa only [stopDrv, retOf, hmin] using h
  have hT0 : 0 ≤ stopTime ⊤ D := stopTime_nonneg ⊤ D
  have hy : c.1 z = (((c.1 z).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre])
  rw [← fwdHull_stopDrv_eq hP hfin]
  constructor
  · rintro ⟨u, hu⟩
    exact Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hWc hT0 hu
  · intro hcl
    have hne' : (c.1 z).re ≠ 0 := fun h => hne (by rw [hy, h, Complex.ofReal_zero])
    rw [hy] at hcl
    obtain ⟨v, hv⟩ := Aux10.exists_isForwardSol_of_notMem_closure hWc hW0 hT0 hne' hcl
    refine ⟨v, ?_⟩
    show IsForwardSol (stopDrv ⊤ D) (c.1 z) (stopTime ⊤ D) v
    rw [hy]
    exact hv

/-- **Hits at a launch**: a real nonzero chart point is hit at the stop iff it is alive before the stop and lies in
the closure of the filled closed trace. -/
theorem lHit_iff {c : Chart} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular D.1 D.2) (hfin : D.2 ≠ ⊤) {z : ℂ}
    (hre : (c.1 z).im = 0) (hne : c.1 z ≠ 0) :
    lHit c ⊤ D z ↔ (∀ r < stopTime ⊤ D, ∃ u, IsForwardSol (stopDrv ⊤ D) (c.1 z) r u) ∧
      c.1 z ∈ closure (fillH (trOf D '' Icc 0 D.2.toNNReal)) := by
  unfold lHit
  rw [lAlive_iff_notMem_closure_fillH hP hfin hre hne, not_not]

end InteractingSLE.Theorem14.SB.Lk
