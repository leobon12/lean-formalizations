/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWGlued
import InteractingSLE.Spec.Sec5.Aux61SlitWPhysical
import InteractingSLE.Spec.Sec5.Aux61SlitWContain
import InteractingSLE.Spec.Sec5.Aux61MarksRead

/-! # The concrete physical source data for the marked assembly -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61Fib Aux61FibData Aux61GInst Aux61ChLoc Aux61ULoc LawUnique GlueCond
universe u

/-- The two records available to the source restart construction. -/
abbrev SourceRecord (nL nR : ℕ) := HistorySpace 0 0 × HistorySpace nL nR

/-- The countable choices owned by the physical restart/window construction.
The chart and selected history event are functions of the initial record. -/
structure SourceRestartData (Ω : Type u) (nL nR : ℕ) where
  ι : Type
  [countable : Countable ι]
  start : ι → ℝ≥0
  selected : ι → Set (SourceRecord nL nR)
  chart : ι → SourceRecord nL nR → Chart
  event : ι → Set (Ω × HistorySpace 0 0)
  path : ι → Ω × HistorySpace 0 0 → ℝ≥0 → ℂ
  contact : ι → Ω × HistorySpace 0 0 → ℝ≥0∞
  data : ι → FibData
  left : ι → ℝ
  right : ι → ℝ

attribute [instance] SourceRestartData.countable

/-- A finite chart interval strictly beyond a live capacity time. Off the
live event its length is zero, as for a killed chart path. -/
def codeSpan (s : FibCode) (q : ℝ≥0) : ℝ≥0 :=
  if hq : (q : ℝ≥0∞) < s.life then
    Classical.choose (ENNReal.lt_iff_exists_nnreal_btwn.1 hq) else 0

/-- The chosen span supplies the actual chart-side trace interval. -/
theorem codeSpan_spec {s : FibCode} (hgood : s ∈ GoodTrace)
    (hinj : InjOn s.trace {t | (t : ℝ≥0∞) ≤ s.life})
    (hint : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < s.life → s.trace t ∈ H)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < s.life) :
    (q : ℝ) < codeSpan s q ∧
      IsLoewnerTraceLT (fun t : ℝ => s.driver t.toNNReal) (codeSpan s q)
        (fun t : ℝ => s.trace t.toNNReal) ∧
      InjOn (fun t : ℝ => s.trace t.toNNReal) (Icc 0 (q : ℝ)) ∧
      ∀ t ∈ Ioc (0 : ℝ) q, s.trace t.toNNReal ∈ H := by
  have hb := Classical.choose_spec (ENNReal.lt_iff_exists_nnreal_btwn.1 hq)
  have he : codeSpan s q = Classical.choose (ENNReal.lt_iff_exists_nnreal_btwn.1 hq) := by
    rw [codeSpan, dite_eq_left hq]
  have hqσ : (q : ℝ≥0∞) < (codeSpan s q : ℝ≥0) := he ▸ hb.1
  have hσ : ((codeSpan s q : ℝ≥0) : ℝ≥0∞) < s.life := he ▸ hb.2
  have hgen : IsGeneratingTrace (s.driver ·) (codeSpan s q) s.trace :=
    ⟨hgood.1, hgood.2.1.mono fun t ht => ht.trans hσ.le,
      fun t ht => hgood.2.2 t (ht.trans hσ)⟩
  refine ⟨NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hqσ),
    Theorem14.CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hgen, ?_, ?_⟩
  · intro t ht v hv heq
    have hle : ∀ w ∈ Icc (0 : ℝ) q, (w.toNNReal : ℝ≥0∞) ≤ s.life := fun w hw =>
      (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hw.2)).trans hq.le
    have h := hinj (hle t ht) (hle v hv) heq
    rwa [Real.toNNReal_eq_toNNReal_iff ht.1 hv.1] at h
  · intro t ht
    exact hint _ (Real.toNNReal_pos.2 ht.1)
      ((ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht.2)).trans_lt hq)

section Data
variable {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ}
  (F : SourceRestartData Ω nL nR) (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
  (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)

/-- The initial retained counterflow and own histories. -/
def sourceRecord (i : F.ι) (p : Ω × HistorySpace 0 0) : SourceRecord nL nR :=
  (stopRec s p.2, stopRec (F.start i) (killedHistory W VL VR ζ p.1))

/-- The R1 chart, fixed by the initial retained record. -/
def sourceChart (i : F.ι) (p : Ω × HistorySpace 0 0) : Chart :=
  F.chart i (sourceRecord F s W VL VR ζ i p)

variable (κ : ℝ) (h : Ω → DistOn upperHalfPlaneOpens)

/-- The selected-access code of the actual physical continuation. -/
def sourceCode (i : F.ι) : Ω × HistorySpace 0 0 → FibCode :=
  accessExitCode (F.event i) (sourceChart F s W VL VR ζ i)
    (F.path i) (F.contact i) (F.data i).V 0 (chiC κ) (fun p => h p.1)

/-- The lifted initial record has the universe of the source probability space. -/
def sourceHistory (i : F.ι) (p : Ω × HistorySpace 0 0) : ULift.{u} (SourceRecord nL nR) :=
  ULift.up (sourceRecord F s W VL VR ζ i p)

/-- The corresponding event in the lifted record space. -/
def sourceHistoryEvent (i : F.ι) : Set (ULift.{u} (SourceRecord nL nR)) :=
  ULift.down ⁻¹' F.selected i

/-- The actual marked chart-complement set, all of `H` off the current
live event. This total version is already relatively closed and nested. -/
def sourceSets (i : F.ι) (q : ℝ≥0) : Ω × HistorySpace 0 0 → Set ℂ :=
  liveSet (liveEv (sourceHistory F s W VL VR ζ i) (sourceHistoryEvent F i)
    (sourceCode F s W VL VR ζ κ h i) q)
    (fun p => chartSet (sourceChart F s W VL VR ζ i p)
      (Aux61UnionK.chartHull (sourceCode F s W VL VR ζ κ h i) q p))

variable (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)

/-- The explicit physical bounded harmonic extension at a rational own time. -/
def sourcePatchExtension (j : ℚ) (ω : Ω) : ℂ → ℝ :=
  Impl.forceExt κ (Ito.weightWord ρL ρR)
    (fun i => VL i (rationalTime j) ω - W (rationalTime j) ω)
    (fun i => VR i (rationalTime j) ω - W (rationalTime j) ω)

/-- Concrete MARKS data: no marks, marked sets, patch sets, means or
comparison events are supplied by an abstract assembly object. -/
def sourceMarksData (η : Ω → ℝ≥0 → ℂ) (μ : Measure (Ω × HistorySpace 0 0)) : MarksData μ where
  ι := F.ι
  β _ := ULift.{u} (SourceRecord nL nR)
  Z := sourceHistory F s W VL VR ζ
  B := sourceHistoryEvent F
  data := F.data
  event := F.event
  chart := sourceChart F s W VL VR ζ
  path := F.path
  life := F.contact
  window := fun i => (F.data i).V
  field := fun p => h p.1
  scale := 0
  constant := chiC κ
  left := F.left
  right := F.right
  originalMean := Impl.forceExt κ (Ito.weightWord ρL ρR) xL xR
  baseMarks := fun i q => nullMarks
    (ruleMarks stopRec (capacityRule (F.chart i) (F.start i) q)
      (fun p => stopRec s p.2) (fun p => killedHistory W VL VR ζ p.1)) μ
  baseSets := sourceSets F s W VL VR ζ κ h
  physicalDriver := fun _ _ p t => W t.toNNReal p.1
  physicalPath := fun _ _ p t => η p.1 t.toNNReal
  start := fun i _ _ => F.start i
  duration := fun i q p => accessTime (E := F.event i)
    (c := sourceChart F s W VL VR ζ i) (ρ := F.path i) (T := F.contact i) (V := (F.data i).V) p q
  domain := fun i _ p => (sourceChart F s W VL VR ζ i p).dom
  chartPath := fun i _ p t => (sourceCode F s W VL VR ζ κ h i p).trace t.toNNReal
  chartLife := fun i q p => codeSpan (sourceCode F s W VL VR ζ κ h i p) q
  index := ℚ
  time := fun j _ _ _ => rationalTime j
  patches := fun j _ _ p => hullAt (rationalTime j) (killedHistory W VL VR ζ p.1)
  mean := fun j _ _ p => couplingMean κ (fun t : ℝ => W t.toNNReal p.1)
    (rationalTime j) (sourcePatchExtension W VL VR κ ρL ρR j p.1)
  physicalMean := fun j _ _ p => sourcePatchExtension W VL VR κ ρL ρR j p.1
  comparisonEvent := fun j i q =>
    liveEv (sourceHistory F s W VL VR ζ i) (sourceHistoryEvent F i)
      (sourceCode F s W VL VR ζ κ h i) 0 ∩
    {p | (rationalTime j : ℝ≥0∞) ≤ capacityRule (F.chart i) (F.start i) q
      (stopRec s p.2, killedHistory W VL VR ζ p.1)}

end Data
end InteractingSLE.Sec5.Aux61SlitW
