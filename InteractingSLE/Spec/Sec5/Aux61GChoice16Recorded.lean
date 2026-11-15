/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GAlignFamily
import InteractingSLE.Spec.Sec5.Aux61SlitWCompare
import InteractingSLE.Spec.Sec5.Aux61GAlignContain
import InteractingSLE.Spec.Sec5.Aux61Asm2R1

/-! # Actual boundary references recorded by the initial source marks

Only own prefixes no later than the retained time are needed for the
initial boundary comparison. Clamping the countable rational reference
times makes every reference recorded by the existing initial marks.
The counterflow reference is read from the same stopped counterflow record.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GChoice16
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61ULoc Aux61Marks
open LawUnique GlueCond
open LocalSets
universe u

/-- The same countable reference family, restricted to retained own times. -/
def pastReferenceIndex (q : ℚ) : SourceReferenceIndex → SourceReferenceIndex
  | .inl j => .inl (min j q)
  | .inr j => .inr j

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)

/-- Every earlier own comparison hull is recorded at zero capacity. -/
theorem own_reference_recorded
    (hchart : ∀ i, Aux61FibData.IsMeasChart (F.chart i)) (i : F.ι) (j : ℚ)
    (hj : rationalTime j ≤ F.start i) :
    Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      (sourceReferenceSet S (.inl j)) := by
  let Y := fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2
  let R := fun p : S.Ω × HistorySpace 0 0 =>
    killedHistory S.own.W S.own.VL S.own.VR S.life p.1
  let rule := capacityRule (F.chart i) (F.start i) 0
  have hm := measurable_comparisonHull Y R rule (rationalTime j)
  have he : (fun p => max (rule p) ((rationalTime j : ℝ≥0) : ℝ≥0∞)) = rule := by
    funext p
    dsimp only [rule]
    rw [capacityRule_zero, max_eq_left (ENNReal.coe_le_coe.2 hj)]
  rw [he] at hm
  obtain ⟨hY, hR⟩ := Aux61Asm2.measurable_initialRecords (S := S)
  have hr : ruleMarks stopRec rule Y R ≤
      (inferInstance : MeasurableSpace (S.Ω × HistorySpace 0 0)) :=
    ruleMarks_le isRecordStop_stopRec
      (measurable_capacityRule (hchart i) (F.start i) 0) hY hR
  exact hm.mono (le_nullMarks hr) le_rfl

/-- The counterflow comparison hull is read from the retained counterflow
record and is therefore recorded at zero capacity. -/
theorem counterflow_reference_recorded
    (hchart : ∀ i, Aux61FibData.IsMeasChart (F.chart i)) (i : F.ι) :
    Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      (sourceReferenceSet S (.inr ())) := by
  obtain ⟨hY, hR⟩ := Aux61Asm2.measurable_initialRecords (S := S)
  have hr := le_nullMarks (μ := S.μ) (ruleMarks_le isRecordStop_stopRec
    (measurable_capacityRule (hchart i) (F.start i) 0) hY hR)
  have hm := measurable_ruleMarks_of_time0
    (Y₀ := fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2)
    (R₀ := fun p => killedHistory S.own.W S.own.VL S.own.VR S.life p.1)
    measurable_fst isRecordStop_stopRec
    (start_le_capacityRule (F.chart i) (F.start i) 0)
  have hk := (GlueCond.measurable_cfHullQ (rationalTime S.s)).comp (hm.mono hr le_rfl)
  have he : (fun p : S.Ω × HistorySpace 0 0 => cfHullQ (rationalTime S.s) p.2) =
      fun p => cfHullQ (rationalTime S.s) (stopRec (rationalTime S.s) p.2) :=
    funext fun p => (CrossCond.Word49.cfHullQ_cfStop (rationalTime S.s) p.2).symm
  rw [show sourceReferenceSet S (.inr ()) =
    (fun p : S.Ω × HistorySpace 0 0 => cfHullQ (rationalTime S.s) p.2) from rfl, he]
  exact hk

/-- Every clamped reference is measurable for the existing initial marks;
no larger marked sigma-algebra is required. -/
theorem past_reference_recorded
    (hchart : ∀ i, Aux61FibData.IsMeasChart (F.chart i)) (i : F.ι) (q : ℚ)
    (hq : F.start i = rationalTime q) (j : SourceReferenceIndex) :
    Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      (sourceReferenceSet S (pastReferenceIndex q j)) := by
  cases j with
  | inl j =>
      apply own_reference_recorded S F hchart i (min j q)
      rw [hq]
      exact Real.toNNReal_le_toNNReal (by exact_mod_cast min_le_right j q)
  | inr j =>
      cases j
      exact counterflow_reference_recorded S F hchart i

variable (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
  (μ := S.μ) S.κ)
include hR

/-- A retained own reference is contained in the actual zero-time marked
set. The optional coupling supplies the regularized physical hull identity. -/
theorem own_reference_subset (i : F.ι) (j : ℚ) (hj : rationalTime j ≤ F.start i)
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ))) :
    ∀ᵐ p ∂S.μ, sourceReferenceSet S (.inl j) p ⊆ (S.marksData F).baseSets i 0 p := by
  have hreg := WangWu.ae_glue_fst (μ := S.P) S.kernel S.measCounterField
    (Sec7.PocketStopWallsFin.ae_regHull_eq S.own.coupling S.own_infinite)
  filter_upwards [source_initial_contains S F hR i hretained, hreg, S.physical_path]
    with p hc hr hp z hz
  have hzH := (sourceReferenceSet_closed S (.inl j) p).1 hz
  apply hc
  simp only [capacityRule_zero, unionAt, ENNReal.coe_lt_top, ↓reduceIte, ENNReal.toNNReal_coe]
  refine ⟨hzH, Or.inr ?_⟩
  rw [hr]
  have hh := Aux50Hit.regHull_stopHistory_cstop hp.1 (rationalTime j)
  change hullAt (rationalTime j) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
    fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime j) at hh
  change z ∈ hullAt (rationalTime j)
    (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) at hz
  rw [hh] at hz
  exact QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 hj) hz

/-- The counterflow reference is contained in the actual zero-time marked
set, including off the live event where that marked set is all of H. -/
theorem counterflow_reference_subset (i : F.ι)
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ))) :
    ∀ᵐ p ∂S.μ, sourceReferenceSet S (.inr ()) p ⊆ (S.marksData F).baseSets i 0 p := by
  filter_upwards [source_initial_contains S F hR i hretained] with p hc z hz
  apply hc
  simp only [capacityRule_zero, unionAt, ENNReal.coe_lt_top, ↓reduceIte, ENNReal.toNNReal_coe]
  exact ⟨(sourceReferenceSet_closed S (.inr ()) p).1 hz, Or.inl hz⟩

/-- All clamped references are contained in the zero-time source set
almost surely, without an additional comparison-containment hypothesis. -/
theorem past_reference_subset (i : F.ι) (q : ℚ) (hq : F.start i = rationalTime q)
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)))
    (j : SourceReferenceIndex) : ∀ᵐ p ∂S.μ,
    sourceReferenceSet S (pastReferenceIndex q j) p ⊆ (S.marksData F).baseSets i 0 p := by
  cases j with
  | inl j =>
      apply own_reference_subset S F hR i (min j q) _ hretained
      rw [hq]
      exact Real.toNNReal_le_toNNReal (by exact_mod_cast min_le_right j q)
  | inr j =>
      cases j
      exact counterflow_reference_subset S F hR i hretained

end InteractingSLE.Sec5.Aux61GChoice16
