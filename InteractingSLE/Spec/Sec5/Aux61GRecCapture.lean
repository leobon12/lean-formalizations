/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GRecIndex
import InteractingSLE.Spec.Sec5.Aux61GHistCountable

/-! # Captured-window subevents from MARKS and slit wiring

Use one restart index on each completed-capture subevent. Its singleton
history cover and completed-window facts follow from the definition of the
subevent. The future capture is never asserted measurable for the past.
Countably many such null subevents exclude the original event.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GRec
open Aux61Marks (MarksData MarksFacts MarksCover)
open Aux61Asm (SlitWiringData SlitWiring)
open Aux61FibData (inPath)

universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- The completed path stays in the selected window before its finite
endpoint, which lands in the forbidden reference interval. The selected
history event is included in this geometric future-capture event. -/
def completedCapture (D : MarksData μ) (i : D.ι) (x : X) : Prop :=
  D.Z i x ∈ D.B i ∧ D.life i x < ⊤ ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < D.life i x →
      inPath (D.event i) (D.chart i) (D.path i) (D.life i) x t ∈ D.window i) ∧
    ∃ y ∈ Ioo (D.left i) (D.right i),
      Tendsto (inPath (D.event i) (D.chart i) (D.path i) (D.life i) x)
        (𝓝[<] (D.life i x).toNNReal) (𝓝 (y : ℂ))

/-- A completed capture has a singleton history cover and the exact
completed-window property required by MARKS. -/
theorem marksCover_completedCapture (D : MarksData μ) (i : D.ι) :
    MarksCover μ (completedCapture D i) (singletonMarks D i) where
  history_cover := ae_of_all _ fun _ hx => ⟨(), hx.1⟩
  completed_window _ := ae_of_all _ fun _ _ hx => hx.2

/-- Each future capture has its own fibre-local cover from the physical
MARKS facts and the existing slit wiring. No separate captured-cover input
or past measurability of the capture is required. -/
theorem localCover_completedCapture [IsProbabilityMeasure μ]
    {D : MarksData μ} (hF : MarksFacts μ D)
    (W : SlitWiringData (D.toAsmData hF)) (hW : SlitWiring μ (D.toAsmData hF) W)
    (i : D.ι) : Aux61UnionK.HasFibreLocalCover μ (completedCapture D i) :=
  Aux61Marks.localCover_of_marks (singletonMarksFacts hF i)
    (marksCover_completedCapture D i) (singletonWiring hF W i)
    (singletonWiring_facts hF W hW i)

/-- Reflected reference avoidance excludes each completed capture. -/
theorem ae_not_completedCapture [IsProbabilityMeasure μ]
    {D : MarksData μ} (hF : MarksFacts μ D)
    (W : SlitWiringData (D.toAsmData hF)) (hW : SlitWiring μ (D.toAsmData hF) W)
    (hneg : Aux61Cov.R5NegStatement.{u}) (i : D.ι) :
    ∀ᵐ x ∂μ, ¬ completedCapture D i x :=
  Aux61Cov.ae_not_of_hasCovFibreCover
    (Aux61Cov.hasCovFibreCover_of_act
      (Aux61Act.hasActFibreCover_of_dy
        (Aux61UnionK.hasDyActFibreCover_of_localCover (localCover_completedCapture hF W hW i))))
    (Aux61Cov.isSettingAvoiding_refWin hneg)

/-- To exclude an event, the remaining capture input is only pointwise
almost-sure coverage by the countably many completed windows. The local
covers of those future subevents are constructed above. -/
theorem ae_not_of_marks_capture_cover [IsProbabilityMeasure μ]
    {D : MarksData μ} (hF : MarksFacts μ D)
    (W : SlitWiringData (D.toAsmData hF)) (hW : SlitWiring μ (D.toAsmData hF) W)
    (hneg : Aux61Cov.R5NegStatement.{u}) {E : X → Prop}
    (hcaptured_cover : ∀ᵐ x ∂μ, E x → ∃ i, completedCapture D i x) :
    ∀ᵐ x ∂μ, ¬ E x := by
  filter_upwards [ae_all_iff.2 (ae_not_completedCapture hF W hW hneg), hcaptured_cover]
    with x hx hc he
  obtain ⟨i, hi⟩ := hc he
  exact hx i hi

end InteractingSLE.Sec5.Aux61GRec
