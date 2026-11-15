/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfPhysCoarse

/-!
# Matching the physical chart transport with the source image field

Packet PROVE-CFCHART2. The field supplied by the optional flow coupling differs
from the original field by the angle constant. Its transported negative is
exactly `imgField`, with the constants of the landed counterflow chart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfPhys

open WangWu LawUnique GlueCond Cond44Ref CfRegQ Prop411Q CfGiven CfConv
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {s : ℝ≥0}

/-- The field transported by the raw chart is measurable as soon as the
original field and killed driving data are measurable. -/
theorem measurable_fChart_transport (hX : IsMeasurableKilledDriving W VL VR ζ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (a k : ℝ) :
    Measurable fun p : Ω × HistorySpace 0 0 => Chart.chartTransport
      (isConformal_fChart (W := W) (VL := VL) (VR := VR) (ζ := ζ) (s := s) p) 1 a k (h p.1) :=
  Chart.measurable_chartTransport_random' (fun p => isConformal_fChart p)
    (fun z => measurableSet_mem_dom_fChart_of (measurable_stopFlow hX s) z)
    (fun z => measurable_indicator_fwd_fChart_of (measurable_stopFlow hX s) z)
    (fun z => measurable_indicator_lift_fChart_of (measurable_stopFlow hX s) z)
    (fun p => continuousOn_lift_fChart p) (hh.comp measurable_fst) 1 a k

/-- Exact agreement with the source image field on a good regular sample. -/
theorem imgField_eq_neg_fChart {κ θ : ℝ} (hκ : 0 < κ) {p : Ω × HistorySpace 0 0}
    (hg : IsGood47 W VL VR ζ p) (he : Exist.Staged.IsRegularDriver ((fun t => W t p.1), ζ p.1))
    {h h' : DistOn upperHalfPlaneOpens} (htr : IsTranslateAddConst 0 (θ * chiC κ) h h') :
    imgField κ (Exist.StagedLaw.recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1)) h =
      -Chart.chartTransport
        (isConformal_fChart (W := W) (VL := VL) (VR := VR) (ζ := ζ) (s := s) p)
        1 ((π - θ) * chiC κ) (chiC κ) h' := by
  rw [imgField_eq_chartTransport hκ]
  simp only [← fChart_eq_cfChart hg he]
  rw [neg_chartTransport]
  ext φ
  let hc := isConformal_fChart (W := W) (VL := VL) (VR := VR) (ζ := ζ) (s := s) p
  have hφ := htr (Chart.pushTest hc φ) (Chart.pushTest hc φ) (fun z => by rw [Complex.ofReal_zero, add_zero])
  have hmass : (∫ z, Chart.pushTest hc φ z) = ∫ z, φ z := by
    simpa only [one_mul] using Chart.integral_mul_pushTest hc φ (fun _ => (1 : ℝ))
  simp only [Chart.chartTransport_apply', one_mul, neg_apply, Chart.oneDist_apply]
  change h' _ = h _ + _ at hφ
  rw [hmass] at hφ
  linarith only [hφ]

end InteractingSLE.Sec5.CfPhys
