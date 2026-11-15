/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketWordPerQSide
import InteractingSLE.Spec.Sec7.StripSysField

/-!
# The actual counterflow objects used by the pocket word

PROVE-POCKET-WORDIN. Extract the witnesses already present in
`IsCenteredCounterflowDriver`. The record contains data only; its transport,
coupling, harmonic-extension, and measurability facts are proved separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketWordIn

/-- The fields, force processes and mean of one centred-counterflow witness. -/
structure CounterflowObjects (κ : ℝ) (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  boundary : ℝ → ℝ
  jumps : Finset ℝ
  sourceField : Ω → DistOn upperHalfPlaneOpens
  field : Ω → DistOn upperHalfPlaneOpens
  filtration : Filtration ℝ≥0 mΩ
  left : Fin (flowLineNL boundary jumps 0) → ℝ≥0 → Ω → ℝ
  right : Fin (flowLineNR boundary jumps 0) → ℝ≥0 → Ω → ℝ
  brownian : ℝ≥0 → Ω → ℝ
  mean : ℂ → ℝ

variable {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The centred driver supplies the exact field-transport and optional-coupling witnesses. -/
theorem exists_counterflowObjects (hc : IsCenteredCounterflowDriver κ P h W ζ) :
    ∃ d : CounterflowObjects κ Ω,
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
        (QuantumZipper.chiC (16 / κ)) (h ω) (d.sourceField ω)) ∧
      (∀ ω, IsTranslateAddConst 0 (0 * QuantumZipper.chiC (16 / κ))
        (d.sourceField ω) (d.field ω)) ∧
      IsOptionalHullCoupling (16 / κ) (flowLineXL d.boundary d.jumps 0)
        (flowLineXR d.boundary d.jumps 0) (flowLineRhoL (16 / κ) d.boundary d.jumps 0 0)
        (flowLineRhoR (16 / κ) d.boundary d.jumps 0 0) P d.filtration W d.left d.right
        d.brownian ζ d.field ∧
      IsBoundedHarmonicExtension
        (forceBoundaryData (16 / κ) (flowLineRhoL (16 / κ) d.boundary d.jumps 0 0)
          (flowLineRhoR (16 / κ) d.boundary d.jumps 0 0)
          (flowLineXL d.boundary d.jumps 0) (flowLineXR d.boundary d.jumps 0))
        (forceJumpSet (flowLineXL d.boundary d.jumps 0) (flowLineXR d.boundary d.jumps 0)) d.mean := by
  obtain ⟨b, J, hs, -, ht, hf, F, VL, VR, B, htr, hC⟩ := hc
  obtain ⟨u, hu⟩ := StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData
    (16 / κ) (flowLineRhoL (16 / κ) b J 0 0) (flowLineRhoR (16 / κ) b J 0 0)
    (flowLineXL b J 0) (flowLineXR b J 0)
  exact ⟨⟨b, J, hs, hf, F, VL, VR, B, u⟩, ht, htr, hC, hu⟩

/-- Choose an actual witness of the given centred driver; there is no default object. -/
def counterflowObjects (hc : IsCenteredCounterflowDriver κ P h W ζ) : CounterflowObjects κ Ω :=
  Classical.choose (exists_counterflowObjects hc)

/-- All field inputs for the chosen witness follow from the centred-driver predicate. -/
theorem counterflowObjects_spec (hc : IsCenteredCounterflowDriver κ P h W ζ) :
    let d := counterflowObjects hc
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (d.sourceField ω)) ∧
    (∀ ω, IsTranslateAddConst 0 (0 * QuantumZipper.chiC (16 / κ))
      (d.sourceField ω) (d.field ω)) ∧
    IsOptionalHullCoupling (16 / κ) (flowLineXL d.boundary d.jumps 0)
      (flowLineXR d.boundary d.jumps 0) (flowLineRhoL (16 / κ) d.boundary d.jumps 0 0)
      (flowLineRhoR (16 / κ) d.boundary d.jumps 0 0) P d.filtration W d.left d.right
      d.brownian ζ d.field ∧
    IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (flowLineRhoL (16 / κ) d.boundary d.jumps 0 0)
        (flowLineRhoR (16 / κ) d.boundary d.jumps 0 0)
        (flowLineXL d.boundary d.jumps 0) (flowLineXR d.boundary d.jumps 0))
      (forceJumpSet (flowLineXL d.boundary d.jumps 0) (flowLineXR d.boundary d.jumps 0)) d.mean :=
  Classical.choose_spec (exists_counterflowObjects hc)

/-- Killed measurability is already part of the actual optional-hull coupling. -/
theorem counterflowObjects_measurable (hc : IsCenteredCounterflowDriver κ P h W ζ) :
    let d := counterflowObjects hc
    IsMeasurableKilledDriving W d.left d.right ζ :=
  (counterflowObjects_spec hc).2.2.1.2.2.2.1

end InteractingSLE.Sec7.PocketWordIn
