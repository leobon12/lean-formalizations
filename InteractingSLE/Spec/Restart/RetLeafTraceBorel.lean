/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalTransport
import InteractingSLE.Spec.Sec7.CounterflowProb2Coding

/-!
# The Borel coding of the generating-trace relation

Packet PROVE-T15-RET. This file proves PROVE-RETPLUMB's named input
`RetAux79.RetCanonicalGeneratingTraceBorel`: on the canonical carrier, the samples whose
continuous decoded trace is a generating trace of the decoded driver through the
recorded lifetime form a Borel set.

For a process `w` with continuous paths from `0`, a measurable random horizon `T` and a
random trace `η` with continuous paths, the event `{IsGeneratingTrace w T η}` is
measurable (`measurableSet_isGeneratingTrace`). The relation is reduced to countably many
conditions:

* through a random horizon `T`, `η` generates iff `η 0 = 0` and it generates through every
  rational `q < T` (`isGeneratingTrace_iff_forall_rat`);
* through a deterministic finite horizon `q`, a continuous `η` generates iff `η 0 = 0`, some
  generating trace through `q` exists, and `η` equals the tip reader `LP.traceAt` at the
  rational times before `q` (`isGeneratingTrace_coe_iff`): two paths continuous before `q`
  that agree at its rational times agree before `q`;
* existence of a generating trace through a deterministic finite horizon is the landed
  countable characterization `Sec7.Coding.exists_isGeneratingTrace_iff_traceCond`, whose
  conditions are measurable in the driver by the same QuantumZipper hull-measurability
  lemmas as `Sec7.Coding.stoppedTraceCodingStatement`
  (`measurableSet_exists_isGeneratingTrace`).

## Main results

* `measurableSet_isGeneratingTrace`;
* **`retCanonicalGeneratingTraceBorel : RetAux79.RetCanonicalGeneratingTraceBorel`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal NNRat
open QuantumZipper (H fwdHull drive)

namespace InteractingSLE.Restart.RetLeaf

open Sec7.Coding

/-! ### Countable reductions of the generating relation -/

/-- Two paths continuous before a horizon that agree at its rational times agree before it. -/
theorem eqOn_of_rat {η η' : ℝ≥0 → ℂ} {T : ℝ≥0∞}
    (hη : ContinuousOn η {t | (t : ℝ≥0∞) < T}) (hη' : ContinuousOn η' {t | (t : ℝ≥0∞) < T})
    (h : ∀ p : ℚ≥0, ((p : ℝ≥0) : ℝ≥0∞) < T → η p = η' p) :
    EqOn η η' {t | (t : ℝ≥0∞) < T} := by
  refine Set.EqOn.of_subset_closure (s := {t : ℝ≥0 | (t : ℝ≥0∞) < T ∧ ∃ p : ℚ≥0, (p : ℝ≥0) = t})
    ?_ hη hη' (fun t ht => ht.1) ?_
  · rintro _ ⟨hT, p, rfl⟩
    exact h p hT
  · intro t ht
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨p, hp1, hp2, hp3⟩ := exists_nnrat_gt_lt ht hε
    refine ⟨p, ⟨hp2, p, rfl⟩, ?_⟩
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 (NNReal.coe_lt_coe.2 hp1))]
    linarith

/-- **Through a deterministic finite horizon**, a continuous path is a generating trace iff it starts
at `0`, some generating trace exists, and the path is the tip reader at the rational times before the
horizon. -/
theorem isGeneratingTrace_coe_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : Continuous η) (q : ℝ≥0) :
    IsGeneratingTrace w q η ↔ η 0 = 0 ∧ (∃ η', IsGeneratingTrace w q η') ∧
      ∀ p : ℚ≥0, ((p : ℝ≥0) : ℝ≥0∞) < q → η p = LP.traceAt p w := by
  constructor
  · intro h
    exact ⟨h.1, ⟨η, h⟩, fun p hp =>
      (LP.traceAt_eq_of_isGeneratingTrace h hw.continuousOn hw0 hp).symm⟩
  · rintro ⟨h0, ⟨η', hη'⟩, hr⟩
    have hagree : EqOn η η' {t | (t : ℝ≥0∞) < (q : ℝ≥0∞)} := by
      refine eqOn_of_rat hη.continuousOn (hη'.2.1.mono fun t (ht : (t : ℝ≥0∞) < q) => le_of_lt ht)
        fun p hp => ?_
      rw [hr p hp, LP.traceAt_eq_of_isGeneratingTrace hη' hw.continuousOn hw0 hp]
    refine ⟨h0, hη.continuousOn, fun t ht => ?_⟩
    have himg : η '' Icc 0 t = η' '' Icc 0 t :=
      Set.image_congr fun x hx => hagree (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hx.2) ht)
    rw [himg]
    exact hη'.2.2 t ht

/-- **Through a random horizon**, a continuous path is a generating trace iff it starts at `0` and
generates through every rational time before the horizon. -/
theorem isGeneratingTrace_iff_forall_rat {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (hη : Continuous η)
    (T : ℝ≥0∞) :
    IsGeneratingTrace w T η ↔
      η 0 = 0 ∧ ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < T → IsGeneratingTrace w (q : ℝ≥0) η := by
  constructor
  · intro h
    exact ⟨h.1, fun q hq => LP.isGeneratingTrace_mono h hq.le⟩
  · rintro ⟨h0, hq⟩
    refine ⟨h0, hη.continuousOn, fun t ht => ?_⟩
    obtain ⟨q, hq1, hq2, -⟩ := exists_nnrat_gt_lt ht one_pos
    exact (hq q hq2).2.2 t (ENNReal.coe_lt_coe.2 hq1)

/-! ### Measurability -/

section Meas

variable {α : Type*} [MeasurableSpace α]

/-- **Existence of a generating trace through a deterministic finite horizon is a measurable event**
of a process with continuous paths from `0`. -/
theorem measurableSet_exists_isGeneratingTrace {w : ℝ≥0 → α → ℝ} (hwm : ∀ t, Measurable (w t))
    (hwc : ∀ a, Continuous (w · a)) (hw0 : ∀ a, w 0 a = 0) (q : ℝ≥0) :
    MeasurableSet {a | ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (w · a) q η} := by
  have hD : ∀ a, drive 1 w a = fun s : ℝ => w s.toNNReal a := fun a => by
    funext s
    simp [QuantumZipper.drive]
  have e : {a | ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (w · a) q η} =
      {a | TraceCond (drive 1 w a) (fun p => LP.traceAt p (w · a))
        (fun p => ((p : ℝ≥0) : ℝ≥0∞) < q)} := by
    ext a
    simp only [mem_ofPred_eq]
    rw [hD a, exists_isGeneratingTrace_iff_traceCond (hwc a) (hw0 a) ENNReal.coe_ne_top]
  rw [e]
  have hτm : ∀ p : ℝ≥0, Measurable fun a => LP.traceAt p (w · a) := fun p =>
    (LP.measurable_traceAt p).comp (measurable_pi_iff.2 hwm)
  have hHm : ∀ p : ℝ≥0, Measurable fun a => LP.traceAt p (w · a) ∈ H := fun p =>
    (measurable_mem.2 QuantumZipper.isOpen_H.measurableSet).comp (hτm p)
  have hKm : ∀ (p : ℝ≥0) (q' : ℚ≥0),
      Measurable fun a => LP.traceAt p (w · a) ∈ fwdHull (drive 1 w a) ((q' : ℝ≥0) : ℝ) :=
    fun p q' => measurableSet_setOfPred.1
      ((QuantumZipper.NonSwallow.measurableSet_fwdHull_prod hwm hwc 1 (NNReal.coe_nonneg _)).preimage
        ((hτm p).prodMk measurable_id))
  refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
  · refine Measurable.forall fun m => Measurable.exists fun k => Measurable.forall fun p : ℚ≥0 =>
      Measurable.forall fun p' : ℚ≥0 => measurable_imp_const fun _ => measurable_imp_const fun _ =>
        measurable_imp_const fun _ => ?_
    exact measurableSet_setOfPred.1 (measurableSet_le ((hτm p).dist (hτm p')) measurable_const)
  · refine Measurable.forall fun q' => measurable_imp_const fun _ => Measurable.and ?_ ?_
    · exact Measurable.forall fun p : ℚ≥0 => measurable_imp_const fun _ => (hHm p).imp (hKm p q')
    · refine Measurable.forall fun ε => Measurable.forall fun c => measurable_imp_const fun hε =>
        measurable_imp_const fun hc => ?_
      have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
      have hcε : (ε : ℝ) < (ratPt c).im := by rw [ratPt_im]; linarith
      refine (Measurable.forall fun p : ℚ≥0 => measurable_imp_const fun _ => measurableSet_setOfPred.1
        (measurableSet_lt measurable_const (measurable_const.dist (hτm p)))).imp
        ((measurable_closedBall_subset_fwdHull hwc hwm (NNReal.coe_nonneg _) hε' hcε).or
          (measurable_disjoint_closedBall_fwdHull hwc hwm q' hε' hcε))

/-- **The generating relation is a measurable event** for a process with continuous paths from `0`, a
measurable random horizon and a random trace with continuous paths. -/
theorem measurableSet_isGeneratingTrace {w : ℝ≥0 → α → ℝ} (hwm : ∀ t, Measurable (w t))
    (hwc : ∀ a, Continuous (w · a)) (hw0 : ∀ a, w 0 a = 0) {T : α → ℝ≥0∞} (hT : Measurable T)
    {η : α → ℝ≥0 → ℂ} (hηm : ∀ t, Measurable fun a => η a t) (hηc : ∀ a, Continuous (η a)) :
    MeasurableSet {a | IsGeneratingTrace (w · a) (T a) (η a)} := by
  have hτm : ∀ p : ℝ≥0, Measurable fun a => LP.traceAt p (w · a) := fun p =>
    (LP.measurable_traceAt p).comp (measurable_pi_iff.2 hwm)
  have e : {a | IsGeneratingTrace (w · a) (T a) (η a)} =
      {a | η a 0 = 0 ∧ ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < T a →
        (∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (w · a) (q : ℝ≥0) η') ∧
          ∀ p : ℚ≥0, ((p : ℝ≥0) : ℝ≥0∞) < ((q : ℝ≥0) : ℝ≥0∞) → η a p = LP.traceAt p (w · a)} := by
    ext a
    simp only [mem_ofPred_eq]
    rw [isGeneratingTrace_iff_forall_rat (hηc a)]
    refine and_congr_right fun h0 => forall_congr' fun q => imp_congr_right fun _ => ?_
    rw [isGeneratingTrace_coe_iff (hwc a) (hw0 a) (hηc a)]
    exact ⟨fun h => h.2, fun h => ⟨h0, h⟩⟩
  rw [e]
  refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
  · exact measurableSet_setOfPred.1 (measurableSet_eq_fun (hηm 0) measurable_const)
  · refine Measurable.forall fun q => ?_
    refine (measurableSet_setOfPred.1 (measurableSet_lt measurable_const hT)).imp (Measurable.and ?_ ?_)
    · exact measurableSet_setOfPred.1 (measurableSet_exists_isGeneratingTrace hwm hwc hw0 _)
    · refine Measurable.forall fun p => measurable_imp_const fun _ => ?_
      exact measurableSet_setOfPred.1 (measurableSet_eq_fun (hηm _) (hτm _))

end Meas

/-- **PROVE-RETPLUMB's Borel coding input, proved**: on the canonical carrier, the samples whose decoded
trace is a generating trace of the decoded driver through the recorded lifetime form a Borel set. -/
theorem retCanonicalGeneratingTraceBorel : RetAux79.RetCanonicalGeneratingTraceBorel :=
  measurableSet_isGeneratingTrace RetAux79.RetCanonSpace.measurable_driver
    RetAux79.RetCanonSpace.continuous_driver RetAux79.RetCanonSpace.driver_zero
    RetAux79.RetCanonSpace.measurable_life RetAux79.RetCanonSpace.measurable_trace
    RetAux79.RetCanonSpace.continuous_trace

end InteractingSLE.Restart.RetLeaf
