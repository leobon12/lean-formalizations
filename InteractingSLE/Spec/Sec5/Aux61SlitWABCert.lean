/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWABDriver

/-! # Borel trace certificates for the stopped counterflow record

The actual good counterflow history supplies both certificates on its
finite retained record. These are predicates of that record alone.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAB
open Aux61R1C Aux61ULoc LawUnique Restart.FlowStopIdentG CfRegQ GlueCond

/-- A driver-certified counterflow record is the stopped killed history
of its continuous driver, with the two empty force words. -/
theorem stopRec_eq_killed_hDrv {y : HistorySpace 0 0} (hy : DyCert y) (s : ℝ≥0) :
    stopRec s y = stopRec s (killedHistory (fun t (_ : Unit) => hDrv y t)
      (fun i => i.elim0) (fun i => i.elim0) (fun _ => ⊤) ()) := by
  apply Prod.ext
  · rfl
  · funext p
    by_cases hp : dyadicTime p ≤ s
    · simp only [stopRec, Sec4.stopHistory, hp, ↓reduceIte,
        killedHistory, ENNReal.coe_lt_top]
      apply Prod.ext
      · exact (hDrv_dyadicTime_of_dyCert hy p).symm
      · exact Subsingleton.elim _ _
    · simp only [stopRec, Sec4.stopHistory, hp, ↓reduceIte]

/-- The counterflow's dyadic certificate gives the finite-record state
certificate, without any future record samples. -/
theorem stateCert_stopRec_of_dyCert {y : HistorySpace 0 0} (hy : DyCert y) (s : ℝ≥0) :
    StateCert s (stopRec s y) := by
  rw [stopRec_eq_killed_hDrv hy s]
  exact stateCert_stopRec_killed (Ω := Unit) (ω := ())
    (W := fun t _ => hDrv y t) (VL := fun i => i.elim0) (VR := fun i => i.elim0)
    (ζ := fun _ => (⊤ : ℝ≥0∞)) rfl hy.zero
    (hy.continuous.prodMk ((continuous_pi fun i => i.elim0).prodMk
      (continuous_pi fun i => i.elim0))) s

/-- The certified frozen driver of a stopped counterflow history reads
the original continuous driver at the minimum of the two times. -/
theorem frozenDrv_stopRec_of_dyCert {y : HistorySpace 0 0} (hy : DyCert y) (s t : ℝ≥0) :
    frozenDrv s (stopRec s y) t = hDrv y (min t s) := by
  rw [stopRec_eq_killed_hDrv hy s]
  exact frozenDrv_stopRec_killed (Ω := Unit) (ω := ())
    (W := fun t _ => hDrv y t) (VL := fun i => i.elim0) (VR := fun i => i.elim0)
    (ζ := fun _ => (⊤ : ℝ≥0∞)) rfl
    (hy.continuous.prodMk ((continuous_pi fun i => i.elim0).prodMk
      (continuous_pi fun i => i.elim0))) s t

/-- On every good counterflow history, its stopped record also certifies
the generating trace up to the retained time. -/
theorem traceCert_stopRec_of_good {y : HistorySpace 0 0} (hy : y ∈ goodCfSet) (s : ℝ≥0) :
    TraceCert s (stopRec s y) := by
  have hS := stateCert_stopRec_of_dyCert hy.1.2 s
  have hc := hS.continuous_frozenDrv
  apply (Sec7.RandRestart.mem_traceSet_iff hc.continuousOn hS.frozenDrv_zero
    fun _ _ => ⟨_, (hc.tendsto _).mono_left nhdsWithin_le_nhds⟩).2
  obtain ⟨N, hN⟩ := exists_nat_gt (s : ℝ)
  have hbig : s < (N : ℝ≥0) + 1 := by
    exact_mod_cast hN.trans (lt_add_one (N : ℝ))
  have hw := hy.1.2.continuous
  obtain ⟨η, hη, -⟩ := (Sec7.RandRestart.mem_traceSet_iff hw.continuousOn hy.1.2.zero
    fun _ _ => ⟨_, (hw.tendsto _).mono_left nhdsWithin_le_nhds⟩).1 (hy.2 N)
  have hgen : IsGeneratingTrace (hDrv y) (s : ℝ≥0∞) η :=
    ⟨hη.1, hη.2.1.mono (fun _ ht => ht.trans (ENNReal.coe_le_coe.2 hbig.le)),
      fun t ht => hη.2.2 t (ht.trans_le (ENNReal.coe_le_coe.2 hbig.le))⟩
  refine Sec7.RandRestart.TraceEvent.congr ⟨η, hgen, fun h => absurd h ENNReal.coe_ne_top⟩ ?_
  intro t ht
  rw [stopRec_eq_killed_hDrv hy.1.2 s,
    frozenDrv_stopRec_killed (Ω := Unit) (ω := ())
      (W := fun t _ => hDrv y t) (VL := fun i => i.elim0) (VR := fun i => i.elim0)
      (ζ := fun _ => (⊤ : ℝ≥0∞)) rfl
      (hw.prodMk ((continuous_pi fun i => i.elim0).prodMk (continuous_pi fun i => i.elim0))),
    min_eq_left (ENNReal.coe_le_coe.1 ht.le)]

/-- Finite counterflow trace certificates form a Borel set of records. -/
def counterflowCertified (s : ℝ≥0) : Set (HistorySpace 0 0) :=
  {y | StateCert s y ∧ TraceCert s y}

theorem measurableSet_counterflowCertified (s : ℝ≥0) : MeasurableSet (counterflowCertified s) :=
  (measurableSet_stateCert s).inter (measurableSet_traceCert s)

theorem stopRec_mem_counterflowCertified {y : HistorySpace 0 0} (hy : y ∈ goodCfSet) (s : ℝ≥0) :
    stopRec s y ∈ counterflowCertified s :=
  ⟨stateCert_stopRec_of_dyCert hy.1.2 s, traceCert_stopRec_of_good hy s⟩

end InteractingSLE.Sec5.Aux61SlitWAB
