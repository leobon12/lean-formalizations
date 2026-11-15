/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceFlow

/-! # Named open inputs from MARKS and the physical restart construction -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW.SourceSetting
open Aux61Marks Aux61ChLoc Aux61ULoc Aux61FibData Aux61GInst LawUnique GlueCond WangWu
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)

/-- Only the open inputs assigned to MARKS and GLUEINST. All objects are
the concrete objects of `marksData`; no `MarksFacts`, `SlitWiring`, union
locality, slit comparison or fibre-cover assertion is assumed. -/
structure Inputs : Prop where
  restart : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ
  code_marks : ∀ i q, (Aux61FibK.codeFiltration.{u} q).comap
    (fun p => ULift.up.{u} ((S.marksData F).code i p)) ≤ (S.marksData F).baseMarks i q
  sets_marks : ∀ i q, Measurable[(S.marksData F).baseMarks i q, hittingSigma]
    ((S.marksData F).baseSets i q)
  chart_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (F.start i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  path_version : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ v : ℝ≥0, 0 < v →
    (v : ℝ≥0∞) < F.contact i p → F.path i p v = S.path p.1 (F.start i + v)
  initial_data : ∀ i, ∃ g : S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
    IsChartGaussAt S.μ ((S.marksData F).Z i) ((S.marksData F).B i) ((S.marksData F).code i) 0
      ((S.marksData F).sigma i 0) g ∧
      Nonempty (Aux61GCont.InitialWindowData (S.Ω × HistorySpace 0 0)
        (S.μ.restrict ((S.marksData F).Z i ⁻¹' (S.marksData F).B i)) (F.data i) g)
  history_cover : ∀ᵐ p ∂S.μ, S.windowEvent p → ∃ i,
    sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i
  completed_window : ∀ i, ∀ᵐ p ∂S.μ,
    sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i →
    S.windowEvent p → F.contact i p < ⊤ ∧
    (∀ v : ℝ≥0, (v : ℝ≥0∞) < F.contact i p →
      inPath (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (F.path i) (F.contact i) p v ∈ (F.data i).V) ∧
    ∃ y ∈ Ioo (F.left i) (F.right i),
      Tendsto (inPath (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (F.path i) (F.contact i) p) (𝓝[<] (F.contact i p).toNNReal) (𝓝 (y : ℂ))

/-- The physical history/endpoint inputs are exactly the cover facts for
the constructed MARKS object. -/
theorem marksCover (I : S.Inputs F) : MarksCover S.μ S.windowEvent (S.marksData F) :=
  ⟨I.history_cover, I.completed_window⟩

/-- The version of the actual path is read from the physical killed own
history before the restart contact. -/
theorem restart_read (I : S.Inputs F) (i : F.ι) : ∀ᵐ p ∂S.μ, p ∈ F.event i →
    ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < F.contact i p →
      F.path i p v = Restart.FlowStopIdentG.histTrace 0
        (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) (F.start i + v) := by
  have hr := ae_histTrace_killedHistory S.own.coupling.1 S.own.trace
    (glueMeasure_fst S.kernel S.measCounterField)
  filter_upwards [I.path_version i, hr, S.physical_path] with p hp hread hg he v hv ht
  rw [hp he v hv ht, hread _ (by rw [hg.1.1]; exact ENNReal.coe_lt_top)]

end InteractingSLE.Sec5.Aux61SlitW.SourceSetting
