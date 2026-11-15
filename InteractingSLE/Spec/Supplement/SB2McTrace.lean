/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MbSeg
import InteractingSLE.Spec.Supplement.SB2FinConfig

/-!
# Trace points are in the closed fill of the trace, and are dead at the stop

Packet PROVE-T14-SB2LIFT (round 17; the `OnSegFill` input of `fillCorr_of_liftImage`, handoff §R16.2 1(c)). In chart
coordinates:

* **`exists_mem_H_trace`**: every time window of positive length inside the life of a generating trace contains a
  time at which the trace is in `ℍ` (the real times have empty interior, `FinRel.interior_post_real_eq_empty`);
* **`trace_mem_closure_fillH`**: a trace point at a positive time `t ≤ T` lies in the closure of
  `fill η([0, T])` (it is a limit of trace points in `ℍ`);
* **`not_lAlive_of_mem_trace`**: a nonzero real chart point on the stopped trace is not alive at the stop
  (`lAlive_iff_notMem_closure_fillH`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

/-- **A generating trace visits `ℍ` in every time window of positive length inside its life.** -/
theorem exists_mem_H_trace {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hηH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → 0 ≤ (η t).im)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbT : ENNReal.ofReal b ≤ T) :
    ∃ s : ℝ, a < s ∧ s < b ∧ η s.toNNReal ∈ H := by
  set S := (a + b) / 2 with hS
  have hS0 : 0 ≤ S := by rw [hS]; linarith
  have hST : ENNReal.ofReal (((0 : ℝ≥0) : ℝ) + S) < T := by
    rw [NNReal.coe_zero, zero_add]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)) hbT
  have hI := FinRel.interior_post_real_eq_empty hη hw hw0 (β' := η) (tL := 0) hS0 hST (fun _ _ => rfl)
  by_contra hne
  push Not at hne
  have hsub : Ioo a S ⊆
      interior {r ∈ Ioo (0 : ℝ) S | η ((0 : ℝ≥0) + r.toNNReal) ∈ {z : ℂ | z.im = 0}} := by
    refine interior_maximal (fun s hs => ⟨⟨by linarith [hs.1], hs.2⟩, ?_⟩) isOpen_Ioo
    have h1 : ¬ (0 < (η s.toNNReal).im) := hne s hs.1 (by linarith [hs.2])
    have h2 := hηH s.toNNReal (show ENNReal.ofReal s ≤ T from
      (ENNReal.ofReal_le_ofReal (by linarith [hs.2])).trans hbT)
    show (η ((0 : ℝ≥0) + s.toNNReal)).im = 0
    rw [zero_add]
    exact le_antisymm (not_lt.1 h1) h2
  rw [hI] at hsub
  have hmem : (a + S) / 2 ∈ Ioo a S := ⟨by linarith, by linarith⟩
  simpa using hsub hmem

/-- **A trace point at a positive time lies in the closed fill of the trace.** -/
theorem trace_mem_closure_fillH {w : ℝ≥0 → ℝ} {T : ℝ≥0} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hηH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → 0 ≤ (η t).im)
    {t : ℝ≥0} (ht0 : 0 < t) (htT : t ≤ T) : η t ∈ closure (fillH (η '' Icc 0 T)) := by
  have hc : ContinuousOn η (Icc 0 T) := hη.2.1.mono fun s hs => ENNReal.coe_le_coe.2 hs.2
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hc t ⟨zero_le, htT⟩) ε hε
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  set a : ℝ := max 0 ((t : ℝ) - δ / 2) with ha
  have hat : a < t := max_lt ht0' (by linarith)
  have hbT : ENNReal.ofReal (t : ℝ) ≤ (T : ℝ≥0∞) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact ENNReal.coe_le_coe.2 htT
  obtain ⟨s, has, hst, hsH⟩ := exists_mem_H_trace hη hw hw0 hηH (le_max_left _ _) hat hbT
  have hs0 : 0 ≤ s := (le_max_left _ _).trans has.le
  have hsT : s.toNNReal ∈ Icc 0 T :=
    ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 (hst.le.trans (by exact_mod_cast htT))⟩
  refine ⟨η s.toNNReal, ⟨hsH, Or.inl (subset_closure ⟨s.toNNReal, hsT, rfl⟩)⟩, ?_⟩
  rw [dist_comm]
  refine hδc hsT ?_
  rw [NNReal.dist_eq, Real.coe_toNNReal _ hs0, abs_sub_lt_iff]
  have : (t : ℝ) - δ / 2 ≤ a := le_max_right _ _
  constructor <;> linarith

/-- **A nonzero real chart point on the stopped trace is dead at the stop.** -/
theorem not_lAlive_of_mem_trace {c : Chart} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular D.1 D.2)
    (hfin : D.2 ≠ ⊤) {z : ℂ} (hre : (c.1 z).im = 0) (hne : c.1 z ≠ 0)
    (ht : c.1 z ∈ trOf D '' Icc 0 D.2.toNNReal) : ¬ lAlive c ⊤ D z := by
  rw [lAlive_iff_notMem_closure_fillH hP hfin hre hne, not_not]
  obtain ⟨t, ht, hzt⟩ := ht
  have hT : ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞) = D.2 := ENNReal.coe_toNNReal hfin
  have hα := isGeneratingTrace_trOf hP
  set w : ℝ≥0 → ℝ := fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal with hwdef
  have hwc : Continuous w := CounterflowRange.continuous_stopped hP.2.1
  have hw0 : w 0 = 0 := by
    have := hP.continuous_stoppedReal.2
    simpa [hwdef] using this
  have hαs : IsGeneratingTrace w ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞) (trOf D) := by
    rw [hT]
    exact CounterflowRange.isGeneratingTrace_stopped hα
  have hH : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ (D.2.toNNReal : ℝ≥0) → 0 ≤ (trOf D u).im := fun u hu =>
    im_nonneg_of_isGeneratingTrace_le hα hP.2.1 hP.1 (hT ▸ hu)
  have ht0 : 0 < t := pos_iff_ne_zero.2 fun h => hne (by rw [← hzt, h]; exact hα.1)
  rw [← hzt]
  exact trace_mem_closure_fillH hαs hwc hw0 hH ht0 ht.2

end InteractingSLE.Theorem14.SB.Lk
