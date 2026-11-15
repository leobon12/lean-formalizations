/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61AsmCover
import InteractingSLE.Spec.Sec5.Aux61SlitVChart

/-!
# The comparison limits from SLIT's wiring

Packet PROVE-AUX61-ASSEMBLE. The field `comparison_limits` of `AsmFacts` (the chart reading of the physical
comparison mean at the smaller flow hulls) is SLIT's `Aux61SlitV.ae_tendsto_chart_sub_flowMean`, applied at each
positive fibre time with the enlarged marks `marks ⊔ germ(time-0 live set)`, the live version of the marked set,
the restart chart extended by the identity off the restart event, and the live versions of the larger unions.
What remains is SLIT's physical wiring (W) (`SlitWiring`): the smaller hulls with their local-set means, the
larger unions marked local with marks containing the conditioning marks, the comparison events, and the chart
constants of the restart code (height offset `0`, lift coefficient `χ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Asm

open Aux61FibData (IsMeasChart chartOf)
open Aux61ChLoc (IsChartGaussAt liveEv liveSet liveSet_of_mem liveSet_of_notMem measurableSet_live)
open Aux61UnionK (HasFibreLocalCover chartHull)
open LocalSets (germSigma IsLocalSetMean lowerUnion)
open WholeField (IsHistoryAvoidanceLocal centredField)

universe u

variable {X : Type u} [mX : MeasurableSpace X] {μ : Measure X}

/-- The marks at fibre time `t` with the time-`0` live germ retained (the marks of `AsmData.sigma`). -/
abbrev AsmData.retainedMarks (D : AsmData μ) (i : D.ι) (t : ℝ≥0) : MeasurableSpace X :=
  D.marks i t ⊔ germSigma (liveSet (liveEv (D.Z i) (D.B i) (D.code i) 0) (D.sets i 0))
    (centredField D.field D.originalMean)

/-- **SLIT's wiring objects** at the positive fibre times: the local-set means of the smaller flow hulls (the
comparison patches of the data), and the larger unions with their marks. -/
structure SlitWiringData (D : AsmData μ) where
  patchMean : D.index → D.ι → ℝ≥0 → X → DistOn upperHalfPlaneOpens
  union : D.index → D.ι → ℝ≥0 → X → Set ℂ
  unionMarks : D.index → D.ι → ℝ≥0 → MeasurableSpace X

/-- **SLIT's wiring facts (W)** at the positive fibre times: the chart constants of the restart code, the marked
sets recorded by their marks, the smaller hulls (relatively closed, every component of their lower union unbounded,
with a local-set mean represented by the comparison mean minus the original mean), and the larger unions (relatively
closed, marked local for marks containing the conditioning marks at the fibre time, containing the marked set and
the smaller hull, equal to the marked set on the comparison event). -/
structure SlitWiring (μ : Measure X) (D : AsmData μ) (W : SlitWiringData D) : Prop where
  scale_eq : D.scale = 0
  constant_eq : ∀ i, D.constant = chiC (D.data i).κ
  sets_marks : ∀ i (t : ℝ≥0), 0 < t → Measurable[D.marks i t, hittingSigma] (D.sets i t)
  patches_measurable : ∀ j i (t : ℝ≥0), 0 < t → Measurable[mX, hittingSigma] (D.patches j i t)
  patches_closed : ∀ j i (t : ℝ≥0), 0 < t → ∀ᵐ x ∂μ, D.patches j i t x ⊆ H ∧ IsOpen (H \ D.patches j i t x)
  patches_unbounded : ∀ j i (t : ℝ≥0), 0 < t → ∀ᵐ x ∂μ, ∀ z ∈ lowerUnion (D.patches j i t x),
    ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (D.patches j i t x)) z)
  patchMean_local : ∀ j i (t : ℝ≥0), 0 < t →
    IsLocalSetMean (D.patches j i t) (centredField D.field D.originalMean) μ (W.patchMean j i t)
  mean_harmonic : ∀ j i (t : ℝ≥0), 0 < t → ∀ᵐ x ∂μ,
    InnerProductSpace.HarmonicOnNhd (D.mean j i t x) (H \ D.patches j i t x)
  mean_represents : ∀ j i (t : ℝ≥0), 0 < t → ∀ᵐ x ∂μ, ∀ φ : TestOn upperHalfPlaneOpens,
    tsupport φ ⊆ H \ D.patches j i t x → W.patchMean j i t x φ = ∫ z, (D.mean j i t x z - D.originalMean z) * φ z
  unionMarks_le : ∀ j i (t : ℝ≥0), 0 < t → W.unionMarks j i t ≤ mX
  union_measurable : ∀ j i (t : ℝ≥0), 0 < t → Measurable[mX, hittingSigma] (W.union j i t)
  union_closed : ∀ j i (t : ℝ≥0), 0 < t → ∀ x, W.union j i t x ⊆ H ∧ IsOpen (H \ W.union j i t x)
  union_local : ∀ j i (t : ℝ≥0), 0 < t →
    IsHistoryAvoidanceLocal (W.unionMarks j i t) (W.union j i t) (centredField D.field D.originalMean) μ
  marks_le : ∀ j i (t : ℝ≥0), 0 < t → D.retainedMarks i t ≤ W.unionMarks j i t
  sets_subset : ∀ j i (t : ℝ≥0), 0 < t → ∀ x, D.sets i t x ∩ H ⊆ W.union j i t x
  patches_marks : ∀ j i (t : ℝ≥0), 0 < t → Measurable[W.unionMarks j i t, hittingSigma] (D.patches j i t)
  patches_subset : ∀ j i (t : ℝ≥0), 0 < t → ∀ x, D.patches j i t x ∩ H ⊆ W.union j i t x
  event_measurable : ∀ j i (t : ℝ≥0), 0 < t → MeasurableSet[D.marks i t] (D.comparisonEvent j i t)
  union_eq : ∀ j i (t : ℝ≥0), 0 < t → ∀ᵐ x ∂μ, x ∈ D.comparisonEvent j i t → W.union j i t x = D.sets i t x

/-- **The comparison limits from SLIT's wiring**: the base facts and SLIT's wiring give all the facts of the
assembly. -/
theorem asmFacts_of_slitWiring [IsProbabilityMeasure μ] {E : X → Prop} (D : AsmData μ)
    (hF : AsmBaseFacts μ E D) (W : SlitWiringData D) (hW : SlitWiring μ D W) : AsmFacts μ E D := by
  refine ⟨hF, ?_⟩
  intro i t g hg ht
  classical
  have hY : Measurable (D.code i) :=
    Aux61GInst.measurable_accessExitCode (hF.spec i) (hF.open_window i) (hF.zero_window i) (hF.landing i)
      (hF.injective_path i) (hF.continuous_lift i) hF.measurable_field
  set h' := centredField D.field D.originalMean with hh'
  set S₀ := liveEv (D.Z i) (D.B i) (D.code i) 0 with hS₀def
  set St := liveEv (D.Z i) (D.B i) (D.code i) t with hStdef
  have hZt : (D.mβ i).comap (D.Z i) ≤ D.marks i t := (hF.Z_le i).trans (hF.marks_mono i t)
  have hS₀m : MeasurableSet[D.marks i 0] S₀ := measurableSet_live (hF.Z_le i) (hF.code_le i 0) (hF.measurable_B i)
  have hStm : MeasurableSet[D.marks i t] St := measurableSet_live hZt (hF.code_le i t) (hF.measurable_B i)
  have hh'm : Measurable h' := WholeField.measurable_centredField hF.measurable_field _
  have hgerm : germSigma (liveSet S₀ (D.sets i 0)) h' ≤ mX :=
    LocalSets.germSigma_le (Aux61Nest.measurable_liveSet (hF.marks_le i 0 _ hS₀m) (hF.sets_measurable i 0)) hh'm
  have hRle : D.retainedMarks i t ≤ mX := sup_le (hF.marks_le i t) hgerm
  have hmt : D.marks i t ≤ D.retainedMarks i t := le_sup_left
  have h0' : D.marks i 0 ≤ D.retainedMarks i t := (hF.marks_mono i t).trans hmt
  have hcm := @IsMeasChart.chartOf X (D.marks i 0) (D.event i) (hF.event_measurable i) (D.chart i)
    (hF.chart_measurable i)
  have hloc : IsHistoryAvoidanceLocal (D.retainedMarks i t) (liveSet St (D.sets i t)) h' μ :=
    Aux61Nest.isHistoryAvoidanceLocal_liveSet_sup_germ hF.zero_field (hF.marks_le i t) hStm
      ((hF.marks_mono i t) _ hS₀m) Aux61OldB.liveEv_subset_zero
      ((hF.sets_zero_measurable i).mono (hF.marks_mono i t) le_rfl) (fun x => (hF.sets_closed i 0 x).1)
      (hF.sets_measurable i t) (hF.sets_mono i t) (hF.locality i t)
  have hgeo : ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (t : ℝ≥0∞) < (D.code i x).life →
      H \ liveSet St (D.sets i t) x = (chartOf (D.event i) (D.chart i) x).2.1 '' (H \ chartHull (D.code i) t x) := by
    filter_upwards [hF.geometry i t] with x hx hxB hxq
    rw [liveSet_of_mem (show x ∈ St from ⟨hxB, hxq⟩),
      Aux61FibData.chartOf_of_mem (Aux61GInst.mem_exitEv_of_lt_accessLife hxq).1.1]
    exact hx hxB hxq
  have hStℳ : ∀ j, MeasurableSet[W.unionMarks j i t] St := fun j =>
    (le_sup_left.trans (hW.marks_le j i t ht)) _ hStm
  have hG : IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) t
      (germSigma (liveSet St (liveSet St (D.sets i t))) h' ⊔ D.retainedMarks i t) g := by
    rw [Aux61Nest.liveSet_idem]
    exact hg
  have hconv := Aux61SlitV.ae_tendsto_chart_sub_flowMean (hF.measurable_B i) hY t hF.measurable_field
    hF.harmonic_originalMean hF.zero_field (Aux61FibData.isConformal_chartOf (hF.spec i).conf) D.scale D.constant
    (fun x _ hq => Aux61GInst.accessExitCode_field_eq (hF.spec i).conf (Aux61GInst.mem_exitEv_of_lt_accessLife hq))
    hRle (hZt.trans hmt) ((hF.code_le i t).trans hmt)
    (fun z => h0' _ (@IsMeasChart.dom X (D.marks i 0) _ hcm z))
    (fun z => (@IsMeasChart.fwd X (D.marks i 0) _ hcm z).mono h0' le_rfl)
    (fun z => (@IsMeasChart.lift X (D.marks i 0) _ hcm z).mono h0' le_rfl)
    (Aux61ChLoc.continuousOn_lift_chartOf (hF.continuous_lift i))
    (Aux61ChLoc.harmonicOnNhd_lift_chartOf (hF.harmonic_lift i))
    (Aux61Nest.measurable_liveSet (hF.marks_le i t _ hStm) (hF.sets_measurable i t))
    (Aux61Nest.liveSet_properties (hF.sets_closed i t)) hloc hgeo
    (L := fun j => D.patches j i t) (g₂ := fun j => W.patchMean j i t)
    (fun j => hW.patches_measurable j i t ht) (fun j => hW.patches_closed j i t ht)
    (fun j => hW.patches_unbounded j i t ht) (fun j => hW.patchMean_local j i t ht)
    (M₂ := fun j => D.mean j i t) (fun j => hW.mean_harmonic j i t ht) (fun j => hW.mean_represents j i t ht)
    (A' := fun j => liveSet St (W.union j i t)) (ℳ := fun j => W.unionMarks j i t)
    (fun j => hW.unionMarks_le j i t ht)
    (fun j => Aux61Nest.measurable_liveSet (hF.marks_le i t _ hStm) (hW.union_measurable j i t ht))
    (fun j => Aux61Nest.liveSet_properties (hW.union_closed j i t ht))
    (fun j => Aux61ChLoc.isHistoryAvoidanceLocal_liveSet (hW.union_local j i t ht) (hStℳ j))
    (fun j => hW.marks_le j i t ht)
    (fun j => Aux61Nest.measurable_liveSet (hStℳ j)
      ((hW.sets_marks i t ht).mono (le_sup_left.trans (hW.marks_le j i t ht)) le_rfl))
    (fun j x => by
      by_cases hx : x ∈ St
      · rw [liveSet_of_mem hx, liveSet_of_mem hx]
        exact hW.sets_subset j i t ht x
      · rw [liveSet_of_notMem hx, liveSet_of_notMem hx]
        exact inter_subset_right)
    (fun j => hW.patches_marks j i t ht)
    (fun j x => by
      by_cases hx : x ∈ St
      · rw [liveSet_of_mem hx]
        exact hW.patches_subset j i t ht x
      · rw [liveSet_of_notMem hx]
        exact inter_subset_right)
    (S' := fun j => D.comparisonEvent j i t) (fun j => hmt _ (hW.event_measurable j i t ht))
    (fun j => by
      filter_upwards [hW.union_eq j i t ht] with x hx hxS
      by_cases hxt : x ∈ St
      · rw [liveSet_of_mem hxt, liveSet_of_mem hxt]
        exact hx hxS
      · rw [liveSet_of_notMem hxt, liveSet_of_notMem hxt])
    hG
  filter_upwards [hconv] with x hx j hxB hxq hxS v hv hrep z₀ hz₀ hball l hl hlim
  have hxE : x ∈ D.event i := (Aux61GInst.mem_exitEv_of_lt_accessLife hxq).1.1
  have hxSt : x ∈ St := ⟨hxB, hxq⟩
  have key := hx j hxB hxq hxS v hv hrep z₀ hz₀ (by rwa [liveSet_of_mem hxSt]) l hl
    (by rwa [Aux61FibData.chartOf_of_mem hxE])
  rw [Aux61FibData.chartOf_of_mem hxE, hW.scale_eq, hW.constant_eq i] at key
  exact key

/-- **The assembled fibre cover from SLIT's wiring.** -/
theorem localCover_of_slitWiring [IsProbabilityMeasure μ] {E : X → Prop} (D : AsmData μ)
    (hF : AsmBaseFacts μ E D) (W : SlitWiringData D) (hW : SlitWiring μ D W) : HasFibreLocalCover μ E :=
  localCover_of_asm D (asmFacts_of_slitWiring D hF W hW)

end InteractingSLE.Sec5.Aux61Asm
