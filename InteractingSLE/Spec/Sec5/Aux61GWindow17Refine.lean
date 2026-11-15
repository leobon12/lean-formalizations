/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Pieces

/-! # Install uniform initial-record window restrictions

This countable family uses the same canonical chart at each retained time.
All selected records have the fixed free seed collar and finite compact
buffer required by their installed window.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61GR1F Aux61GInst Aux61GWord Aux61FibData LawUnique
universe u

/-- A retained time, a rational landing interval and an allowed window. -/
abbrev RefinedIndex (S : SourceSetting.{u}) := GoodTime S × ReferenceInterval × AllowedWindow

/-- The source choices with the constructed Borel restrictions installed. -/
def refinedChoices (S : SourceSetting.{u}) : RestartChoices S where
  ι := RefinedIndex S
  q i := i.1.1
  selected i := windowRecords S i.1 i.2.2
  data i := referenceWindowData S.κ_pos (intervalWord S i.2.1) (windowGeometry i.2.2.1.1)
  left i := (intervalWord S i.2.1).left
  right i := (intervalWord S i.2.1).right

/-- The fully normalized, uniformly localized actual source family. -/
abbrev refinedFamily (S : SourceSetting.{u}) := canonicalFamily (refinedChoices S)

theorem refinedChoices_selected_measurable (S : SourceSetting.{u}) :
    ∀ i, MeasurableSet ((refinedChoices S).selected i) :=
  fun i => measurableSet_windowRecords S i.1 i.2.2

theorem refinedChoices_window_fields (S : SourceSetting.{u}) :
    WindowFields (refinedChoices S).toR1Restart where
  open_window i := (windowGeometry i.1.2.2.1.1).open_window
  zero_window i := (windowGeometry i.1.2.2.1.1).zero_window
  clearance _ := rfl
  kappa _ := rfl
  reference i := (intervalWord S i.1.2.1).reference

/-- Each fixed family's existing compact buffer is physically finite
on every selected sample, rather than merely on an existential candidate. -/
theorem refinedFamily_finite_buffer (S : SourceSetting.{u}) (i : (refinedChoices S).Idx)
    (p : S.Ω × HistorySpace 0 0) (he : p ∈ (refinedFamily S).event i) :
    ∀ z ∈ closure ((refinedFamily S).data i).buffer ∩ Hbar,
      boundedInverse (sourceChart (refinedFamily S) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p) z ≠ 1 :=
  he.1.2.1

/-- Each selected record has a bounded physical inverse-window image. -/
theorem refinedFamily_inverse_bounded (S : SourceSetting.{u}) (i : (refinedChoices S).Idx)
    (p : S.Ω × HistorySpace 0 0) (he : p ∈ (refinedFamily S).event i) :
    Bornology.IsBounded ((sourceChart (refinedFamily S) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life i p).2.1 '' (((refinedFamily S).data i).V ∩ H)) :=
  isBounded_inverse_on_windowRecords S i.1.1 i.1.2.2 he.1

/-- The installed windows have uniform free seed collars on their actual
selected events. The old boundary is the physical counterflow boundary. -/
theorem refinedFamily_seed (S : SourceSetting.{u}) : ∀ i, ∀ᵐ p ∂S.μ,
    p ∈ (refinedFamily S).event i → ∀ a : ℝ,
      |a| < ((i.1.2.2.1.1 : WindowIndex).2.2 : ℝ) →
      boundedInverse (sourceChart (refinedFamily S) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p) (a : ℂ) ∉
        oldModelBoundary (counterflowRecord (WangWu.histLine p.2) (rationalTime S.s)) := by
  intro i
  filter_upwards [S.counterflow_good] with p hcf he a ha
  have hf := seed_on_windowRecords S i.1.1 i.1.2.2 he.1 ha
  change boundedInverse (sourceChart (refinedFamily S) (rationalTime S.s)
    S.own.W S.own.VL S.own.VR S.life i p) (a : ℂ) ∉
    Aux61SlitWAB.recordBoundary (rationalTime S.s) (Aux61ULoc.stopRec (rationalTime S.s) p.2) at hf
  rwa [Aux61SlitWAB.recordBoundary_stopRec_eq hcf.1.1.2] at hf

end InteractingSLE.Sec5.Aux61GWindow17
