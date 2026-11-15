/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfPhysRaw
import InteractingSLE.Spec.Restart.DomainMarkovAux79Line

/-!
# Physical marked union locality gives raw image members

Packet PROVE-CFCHART2. Apply the landed conformal local-set decomposition and
projection identity at deterministic physical lines, then the strict dyadic
passage. The physical set is the actual union of the stopped flow hull and the
reflected counterflow hull; its domain identity is already proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfPhys

open WangWu LawUnique GlueCond Cond44Ref CfRegQ Prop411Q Coupling LocalSets WholeField
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Restart.DomainMarkov Restart.DomainMarkov.K2
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq)
open CrossCond.Word49 (dyqR dyqR_toNNReal)

/-- The deterministic stopped-history chart has a harmonic lift. -/
theorem harmonicOnNhd_lift_fChartH {nL nR : ℕ} (s : ℝ≥0) (y : HistorySpace nL nR) :
    InnerProductSpace.HarmonicOnNhd (fChartH s y).2.2 (fChartH s y).dom := by
  let w := regDrvH y
  have hw : Continuous w := continuous_regDrvH y
  have h0 : w 0 = 0 := regDrvH_zero y
  have ho := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw s.coe_nonneg
  have hf := QuantumZipper.FwdHolo.differentiableOn_fwdMap hw s.coe_nonneg
  have hmap : MapsTo (QuantumZipper.fwdMap w s) (H \ fwdHull w s) H :=
    fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hw s.coe_nonneg hz
  have hc : InnerProductSpace.HarmonicOnNhd
      (infinitySourceChart.2.2 ∘ QuantumZipper.fwdMap w s) (H \ fwdHull w s) :=
    LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H ho
      Sec7.StripSysField.harmonicOnNhd_infinitySourceChart_lift hf hmap
  rw [show ((fChartH s y).dom : Set ℂ) = H \ fwdHull w s from coe_dom_fChartH y]
  intro z hz
  have hl : InnerProductSpace.HarmonicAt (fun z => (QuantumZipper.logDerivFwd w s z).im) z :=
    ((isDerivLog_fwdMap hw s.coe_nonneg).1.analyticAt (ho.mem_nhds hz)).harmonicAt_im
  have he : (fChartH s y).2.2 = fun z =>
      infinitySourceChart.2.2 (QuantumZipper.fwdMap w s z) + (QuantumZipper.logDerivFwd w s z).im := by
    funext z
    exact fChartH_lift y z
  rw [he]
  exact (hc z hz).add hl

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR mL mR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}
  {xL : Fin mL → ℝ} {xR : Fin mR → ℝ} {μ : Measure (Ω × HistorySpace 0 0)} [IsProbabilityMeasure μ]

/-- Raw image members follow from the history-marked locality of the physical
unions at deterministic lines. The inverse-clock and announcing-event passage
is proved here, and is not an additional premise. -/
theorem hasSafeMembers_fChart_of_unionLocal (hY : IsMeasurableKilledDriving W VL VR ζ)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hgood : ∀ᵐ p ∂μ, p ∈ E)
    {h : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens} (hh : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) μ)
    (hloc : ∀ n k, IsHistoryAvoidanceLocal (CrossCond.cfGlueMarks W VL VR ζ s (dyq n k))
      (fun p => hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ (dyq n k) p.2)
      (centredField h u₀) μ) (a k : ℝ) :
    HasSafeMembers μ (qRaw xL xR W VL VR ζ s E) univ
      (fun p => qT W VL VR ζ s E p) (qW W VL VR ζ s E)
      (fun p => Chart.chartTransport (isConformal_fChart (W := W) (VL := VL) (VR := VR) (ζ := ζ) (s := s) p)
        1 a k (h p)) := by
  have hstop : ∀ n j, Measurable[CrossCond.cfGlueMarks W VL VR ζ s (dyq n j)]
      (flowStop W VL VR ζ s) := by
    intro n j
    have hm := measurable_fst.comp (measurable_stopD47 (W := W) (VL := VL) (VR := VR) (ζ := ζ) s (dyqR n j))
    rw [dyqR_toNNReal] at hm
    exact hm
  have hXm : Measurable fun p => Chart.chartTransport
      (isConformal_fChart (W := W) (VL := VL) (VR := VR) (ζ := ζ) (s := s) p) 1 a k (h p) :=
    Chart.measurable_chartTransport_random'
      (fun p => isConformal_fChart (W := W) (VL := VL) (VR := VR) (ζ := ζ) (s := s) p)
      (fun z => (CrossCond.cfGlueMarks_le _ _ hY) _ (measurableSet_mem_dom_fChart_of (hstop 0 0) z))
      (fun z => (measurable_indicator_fwd_fChart_of (hstop 0 0) z).mono
        (CrossCond.cfGlueMarks_le _ _ hY) le_rfl)
      (fun z => (measurable_indicator_lift_fChart_of (hstop 0 0) z).mono
        (CrossCond.cfGlueMarks_le _ _ hY) le_rfl) (fun p => continuousOn_lift_fChart p) hh 1 a k
  refine hasSafeMembers_qRaw_of_lineMembers hY hEg hgood hXm ?_
  intro n j Fb hFb D hD hDs f Ξ
  let F : Set (Ω × HistorySpace 0 0) := {p | (dyq n j : ℝ) ∈ qgPre W VL VR ζ s E p}
  let r : Ω × HistorySpace 0 0 → ℝ≥0 :=
    fun p => (capClock (qgCurve W s E p) (dyq n j)).toNNReal
  have hBm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 =>
      hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ (dyq n j) p.2 :=
    (CrossCond.measurable_union_cfGlueMarks s (dyq n j)).mono
      (CrossCond.cfGlueMarks_le _ _ hY) le_rfl
  refine Restart.DomainMarkov.Aux79.setIntegral_lapTest_of_lineLocal (ζ := fun p => qT W VL VR ζ s E p)
    (W := qW W VL VR ζ s E) (F := F) hh hu₀ hh0
    (fun p => isConformal_fChart (W := W) (VL := VL) (VR := VR) (ζ := ζ) (s := s) p)
    (CrossCond.cfGlueMarks_le _ _ hY) (fun z => measurableSet_mem_dom_fChart_of (hstop n j) z)
    (fun z => measurable_indicator_fwd_fChart_of (hstop n j) z)
    (fun z => measurable_indicator_lift_fChart_of (hstop n j) z)
    (fun p => continuousOn_lift_fChart p)
    (fun p => harmonicOnNhd_lift_fChartH s (flowStop W VL VR ζ s p)) a k r _ hBm
    (fun p => CrossCond.union_relClosed s (dyq n j) _ p.2) (hloc n j) ?_ ?_ Fb hFb hD ?_ f Ξ
  · filter_upwards [hgood] with p hp hpF _
    exact (fChart_inv_image_eq hEg hp hpF).symm
  · exact ae_of_all _ fun p _ =>
      ⟨(isKilledCurve_qgCurve hEg p).continuousOn_kcW, (isKilledCurve_qgCurve hEg p).kcW_zero⟩
  · filter_upwards [hDs] with p hp hpD
    have hsafe := hp hpD
    refine ⟨hsafe.1, (isKilledCurve_qgCurve hEg p).lt_kcLife hsafe.1, ?_⟩
    change Disjoint _ (fwdHull _ ((capClock (qgCurve W s E p) (dyq n j)).toNNReal : ℝ))
    rw [Real.coe_toNNReal _ ((isKilledCurve_qgCurve hEg p).capClock_nonneg hsafe.1)]
    exact hsafe.2

end InteractingSLE.Sec5.CfPhys
