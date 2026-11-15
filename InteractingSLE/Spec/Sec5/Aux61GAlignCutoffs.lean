/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GAlignCompare

/-! # The source boundary proof constructs the correction and cutoffs

The actual mean is harmonic on the selected event because the code is alive
there at zero. Pull back the record-law boundary property and reuse the
measurable correction and reflected-cutoff construction on that event.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GAlign
open Aux61SlitW Aux61SlitW.SourceSetting Aux61Marks Aux61ChLoc Aux61GCont
open LawUnique GlueCond
universe u

/-- A retained record's boundary property and an actual initial Gaussian
law construct the physical correction and cutoffs. No cutoff family or
initial representative is assumed. -/
theorem nonempty_initialWindowData_of_record_boundary
    {X : Type u} [mX : MeasurableSpace X] {μ : Measure X}
    (D : MarksData μ) (i : D.ι) (hB : MeasurableSet (D.B i))
    {g : X → DistOn upperHalfPlaneOpens}
    (hG : IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0 (D.sigma i 0) g)
    (hlive : ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (0 : ℝ≥0∞) < (D.code i x).life)
    (hboundary : D.InitialBoundary i g) :
    Nonempty (InitialWindowData X (μ.restrict (D.Z i ⁻¹' D.B i)) (D.data i) g) := by
  have hZ : Measurable (D.Z i) := Measurable.of_comap_le (hG.marksZ.trans hG.le)
  have hg : Measurable g := hG.measurable.mono hG.le le_rfl
  have hH : ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → IsHarmonicDistOn (g x) H := by
    filter_upwards [hG.harmonic, hlive] with x hx hl hxB
    have hh := hx hxB (hl hxB)
    rwa [Aux61OldB.chartHull_zero, sdiff_empty] at hh
  have hb := (Aux61GRec.initialBoundary_iff_physical D i hZ hB hg).1 hboundary
  apply Aux61GCont.nonempty_initialWindowData (D.data i) hg
    ((ae_restrict_iff' (hB.preimage hZ)).2 hH)
  apply (ae_restrict_iff' (hB.preimage hZ)).2
  filter_upwards [hb, hH] with x hx hh hxB
  exact hx hxB (hh hxB)

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
    (μ := S.μ) S.κ)
include hR

/-- The concrete source's initial Gaussian law, record boundary values,
and measurable correction/cutoff data from physical comparison inputs.
This discharges the existential initial-data input without assuming it. -/
theorem exists_source_initial_data (i : F.ι)
    (hsets : Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      ((S.marksData F).baseSets i 0))
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)))
    (C : ZeroComparisons (S.marksData F) i) :
    ∃ g : S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      @IsChartGaussAt (S.Ω × HistorySpace 0 0) _
        ((S.marksData F).β i) ((S.marksData F).mβ i)
        S.μ ((S.marksData F).Z i) ((S.marksData F).B i)
        ((S.marksData F).code i) 0 ((S.marksData F).sigma i 0) g ∧
      (S.marksData F).InitialBoundary i g ∧
      Nonempty (InitialWindowData (S.Ω × HistorySpace 0 0)
        (S.μ.restrict ((S.marksData F).Z i ⁻¹' (S.marksData F).B i)) (F.data i) g) := by
  obtain ⟨g, hG⟩ := exists_source_initialGauss_of_retained S F hR i hsets hretained
  have hbd := source_initialBoundary_of_comparisons S F hR i hsets hretained C hG
  refine ⟨g, hG, hbd, nonempty_initialWindowData_of_record_boundary (S.marksData F) i
    (measurable_down (hR.selected_measurable i)) hG ?_ hbd⟩
  filter_upwards [source_zero_alive_iff S F hR i] with p hp hB
  exact hp.2 hB

end InteractingSLE.Sec5.Aux61GAlign
