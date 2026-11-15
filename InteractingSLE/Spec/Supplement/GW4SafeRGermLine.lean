/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRGermReal

/-!
# GW4: the reference input after real connectors are discharged

The current chart and word are evaluated at the actual random physical-line
clock. Surviving real accesses use the proved exact initial height. Only the
other accesses need old-reference increment laws and own-height collars.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Sec7.PhaseSel Sec7.PocketStopSide
  Sec7.Aux119Heights Supp8.Q3Stop LocalSets WholeField MartChar

/-- The actual own chart at the random clock of one physical line. -/
def componentLineChart {Ω : Type*} (F : Frame) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : Chart :=
  Chart.id.loewner (wpath R ω) (lineClock F Wd GT V t ω).toNNReal

/-- The exact surviving force jumps at the same physical line. -/
def componentLineJumps {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord) (F : Frame)
    (X : Ω → DistOn upperHalfPlaneOpens) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : Set ℝ :=
  let q := (lineClock F Wd GT V t ω).toNNReal
  forceJumpSet (fun i => componentVL k c₀ X R V i q ω - R q ω)
    (fun j => componentVR k c₀ X R V j q ω - R q ω)

/-- The full finite word, with the specified common phase, at the line clock. -/
def componentLinePhaseData {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord) (F : Frame)
    (X : Ω → DistOn upperHalfPlaneOpens) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (d : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (ξ : ℝ) : ℝ :=
  let q := (lineClock F Wd GT V t ω).toNNReal
  phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
    (fun i => componentVL k c₀ X R V i q ω - R q ω)
    (fun j => componentVR k c₀ X R V j q ω - R q ω) (d q ω) ξ

/-- A certified surviving real access with its exact finite-word label.
This is geometric/mark matching data; its mean limit is proved separately. -/
def ComponentRealAccess {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord) (F : Frame)
    (X : Ω → DistOn upperHalfPlaneOpens) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (d : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (ξ : ℝ) : Prop :=
  ∃ (x : ℝ) (a : ℝ → ℂ), x ∉ c₀.jumps ∧
    QuantumZipper.IsForwardSol (wpath R ω) x (lineClock F Wd GT V t ω).toNNReal a ∧
    ξ = (a (lineClock F Wd GT V t ω).toNNReal).re ∧
    c₀.fn x = componentLinePhaseData k c₀ F X Wd GT R V d t ω ξ

/-- **Open source input.** One retained current mean per physical line,
countably many old references with their actual increment laws, and a cover
of the accesses not already certified as surviving real connectors.
There is no current-mean boundary limit or reference-selection measurability
assumption. The old heights and lift discrepancies still require proof. -/
def ComponentReferenceInputs {Ω : Type*} [MeasurableSpace Ω]
    (k : ℝ) (c₀ : BoundaryWord) (F : Frame) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : Ω → DistOn upperHalfPlaneOpens) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ)
    (B : ℝ≥0 → Ω → Set ℂ) (d : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t, ∃ g : Ω → DistOn upperHalfPlaneOpens,
    IsLocalSetMean (B t) (centredField X u₀) ν g ∧
    ∃ (old : ℕ → Ω → Chart) (gOld : ℕ → Ω → DistOn upperHalfPlaneOpens)
        (M : ℕ → Set Ω),
      (∀ i ω, ω ∈ M i → lineClock F Wd GT V t ω < V ω ∧
        (old i ω).IsConformal ∧
        ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) ⊆ (old i ω).dom) ∧
      (∀ i, ∀ᵐ ω ∂ν, ω ∈ M i → IsHarmonicDistOn (gOld i ω) (old i ω).dom) ∧
      (∀ i, HasOldChartIncrementLaw ν (M i) (old i)
        (componentLineChart F Wd GT R V t) (gOld i) g) ∧
      IncidentReferenceCover ν k {ω | lineClock F Wd GT V t ω < V ω}
        old (componentLineChart F Wd GT R V t) gOld M u₀
        (fun ω => componentLineJumps k c₀ F X Wd GT R V t ω ∪
          {ξ | ComponentRealAccess k c₀ F X Wd GT R V d t ω ξ})
        (componentLinePhaseData k c₀ F X Wd GT R V d t)

end InteractingSLE.Theorem14.GW4Fix
