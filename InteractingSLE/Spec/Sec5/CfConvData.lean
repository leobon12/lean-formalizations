/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvRecord

/-!
# Geometric coordinates and traces of the infinite image chain

Packet PROVE-CFCHART2. Before an infinite killing time the killed mark coordinates are exactly
the geometric Loewner images. The canonical image trace generates the chain at all finite times.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfConv

open LawUnique CfGiven CfChart
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Restart Sec7.PocketTraversal

section Trace

variable {γ : ℝ → ℂ} {S : Set ℝ}

/-- At infinite terminal capacity the killed trace generates the chain through every finite time. -/
theorem isGeneratingTrace_kcTr_top (hγ : IsKilledCurve γ S) (htop : kcLife γ S = ⊤) :
    IsGeneratingTrace (kcW γ S) ⊤ (kcTr γ S) := by
  have hfin : ∀ T : ℝ≥0, IsGeneratingTrace (kcW γ S) T (kcTr γ S) := fun T =>
    hγ.isGeneratingTrace_kcTr (by rw [htop]; exact ENNReal.coe_lt_top)
  refine ⟨(hfin 1).1, fun t _ => ?_, fun t _ => (hfin (t + 1)).2.2 t ?_⟩
  · exact (hγ.isDrivenCurve.continuousAt_capTrace (by
      change (t : ℝ≥0∞) < kcLife γ S
      rw [htop]
      exact ENNReal.coe_lt_top)).continuousWithinAt
  · exact ENNReal.coe_lt_coe.2 (lt_add_one t)

end Trace

section Marks

variable {Z Ω : Type*} {nL nR mL mR : ℕ} {W : ℝ≥0 → Z → ℝ}
  {VL : Fin nL → ℝ≥0 → Z → ℝ} {VR : Fin nR → ℝ≥0 → Z → ℝ} {ζ : Z → ℝ≥0∞}
  {s : ℝ≥0} {E : Set (Z × HistorySpace 0 0)} {ι : Ω → Z × HistorySpace 0 0}
  {x : Fin mL → ℝ} {y : Fin mR → ℝ} {V : ℝ≥0 → Ω → ℝ}
  {xL : Ω → Fin (mL + 1) → ℝ} {xR : Ω → Fin (mR + 1) → ℝ} {ω : Ω}

/-- The left killed marks are geometric images whenever the new driver and initial marks agree. -/
theorem qVL_eq_geomLW (htop : qT W VL VR ζ s E (ι ω) = ⊤)
    (hV : ∀ t, V t ω = qW W VL VR ζ s E t (ι ω))
    (hx : xL ω = qgXL x W s E (ι ω)) (i : Fin (mL + 1)) (t : ℝ≥0) :
    qVL x W VL VR ζ s E i t (ι ω) = geomLW V xL i t ω := by
  have ht : (t : WithTop ℝ≥0) < kcLife (qgCurve W s E (ι ω)) (qgPre W VL VR ζ s E (ι ω)) := by
    change (t : WithTop ℝ≥0) < qT W VL VR ζ s E (ι ω)
    rw [htop]
    exact WithTop.coe_lt_top t
  rw [qVL, kcVL_of_lt _ _ ht]
  change -(WangWu.ImgWord.kImg (fun r => -kcPath (qgCurve W s E (ι ω))
    (qgPre W VL VR ζ s E (ι ω)) r) (-(qgXL x W s E (ι ω) i)) t) =
    -(MartChar.RealFlow.rightImg (fun r => -V r.toNNReal ω) (-xL ω i) t)
  simp only [WangWu.ImgWord.kImg, kcPath, hx, hV, qW]

/-- The right killed marks are geometric images whenever the new driver and initial marks agree. -/
theorem qVR_eq_geomRW (htop : qT W VL VR ζ s E (ι ω) = ⊤)
    (hV : ∀ t, V t ω = qW W VL VR ζ s E t (ι ω))
    (hx : xR ω = qgXR y W s E (ι ω)) (j : Fin (mR + 1)) (t : ℝ≥0) :
    qVR y W VL VR ζ s E j t (ι ω) = geomRW V xR j t ω := by
  have ht : (t : WithTop ℝ≥0) < kcLife (qgCurve W s E (ι ω)) (qgPre W VL VR ζ s E (ι ω)) := by
    change (t : WithTop ℝ≥0) < qT W VL VR ζ s E (ι ω)
    rw [htop]
    exact WithTop.coe_lt_top t
  rw [qVR, kcVR_of_lt _ _ ht]
  change WangWu.ImgWord.kImg (kcPath (qgCurve W s E (ι ω)) (qgPre W VL VR ζ s E (ι ω)))
    (qgXR y W s E (ι ω) j) t = MartChar.RealFlow.rightImg (fun r => V r.toNNReal ω) (xR ω j) t
  simp only [WangWu.ImgWord.kImg, hx, hV, qW]
  rfl

end Marks

section Observe

variable {Ω R : Type*} [MeasurableSpace R] [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {nL nR : ℕ} {κ a k : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- Add a record at time zero. -/
def recordFiltration (𝓐 : Filtration ℝ≥0 mΩ) (r : Ω → R) (hr : Measurable r) : Filtration ℝ≥0 mΩ :=
  𝓐 ⊔ Filtration.const ℝ≥0 (MeasurableSpace.comap r inferInstance) hr.comap_le

theorem IsChartCanon.observe_record {r : Ω → R} (hr : Measurable r) (hh : Measurable h)
    (hrec : ∀ t, MeasurableSpace.comap r inferInstance ≤ aeSigma P (𝓐 t))
    (hcan : IsChartCanon κ ρL ρR P 𝓐 W VL VR ζ c a k h) :
    IsChartCanon κ ρL ρR P (recordFiltration 𝓐 r hr) W VL VR ζ c a k h :=
  CfChart.IsChartCanon.of_le_aeSigma hcan hh (fun _ => le_sup_left)
    (fun t => sup_le (le_aeSigma _ _) (hrec t))

end Observe

end InteractingSLE.Sec5.CfConv
