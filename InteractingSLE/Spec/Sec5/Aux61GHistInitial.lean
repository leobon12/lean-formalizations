/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GHistReference
import InteractingSLE.Spec.Sec5.Aux61GStepZero

/-! # Local boundary comparison suffices for correction and cutoff selection

The reference continuation makes the off-event boundary condition automatic.
The on-event boundary comparison remains a named mathematical input. The
resulting data identify the actual, rather than an assumed factored, initial
Gaussian mean.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GHist
open Aux61Fib (FibData FibCode)
open Aux61GCont (InitialWindowData)
open Aux61ChLoc (IsChartGaussAt IsChartMeanAt)

/-- Boundary comparison is only needed on the selected history event;
the reference continuation supplies its complement. The existing reflection
and measurable cutoff construction then produce all initial window data. -/
theorem nonempty_initialWindowData_of_local_history_boundary
    {β : Type*} [MeasurableSpace β] {ν : Measure β} (d : FibData)
    {B : Set β} {T₀ : β → DistOn upperHalfPlaneOpens}
    (hT₀ : Measurable T₀) (hharm : ∀ᵐ b ∂ν, IsHarmonicDistOn (T₀ b) H)
    (hoff : ∀ b ∉ B, T₀ b = referenceDist d)
    (hboundary_on_history : ∀ᵐ b ∂ν, b ∈ B → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T₀ b ψ = ∫ z, v z * ψ z) →
      ∀ a ∈ d.O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 d z)
        (𝓝[H] (a : ℂ)) (𝓝 0)) :
    Nonempty (InitialWindowData β ν d T₀) := by
  apply Aux61GCont.nonempty_initialWindowData d hT₀ hharm
  filter_upwards [hboundary_on_history] with b hb
  intro v hv hrep a ha
  by_cases hbB : b ∈ B
  · exact hb hbB v hv hrep a ha
  · have href : ∀ ψ : TestOn upperHalfPlaneOpens,
        referenceDist d ψ = ∫ z, v z * ψ z := by
      simpa only [hoff b hbB] using hrep
    have he : EqOn v (Aux61GlueK.refMean0 d) H := eqOn_reference_of_pairings d hv href
    have hev : (fun z => v z - Aux61GlueK.refMean0 d z) =ᶠ[𝓝[H] (a : ℂ)] fun _ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_eq_zero.2 (he hz)
    exact tendsto_const_nhds.congr' hev.symm

universe u v
variable {X : Type u} {𝒢₀ : MeasurableSpace X} [mX : MeasurableSpace X]
  {β : Type*} [mβ : MeasurableSpace β] {μ : Measure X} [IsFiniteMeasure μ]
  {Z : X → β} {B : Set β} {Y : X → FibCode}
  {d : FibData} {T₀ : β → DistOn upperHalfPlaneOpens}
  {h₀ : X → DistOn upperHalfPlaneOpens}

/-- The constructed initial data give (K-b) for the actual initial
decomposition whenever their history distribution agrees on B. -/
theorem isChartMeanAt_zero_of_history_factor (hZ : Measurable Z)
    (hY : Measurable Y) (hB : MeasurableSet B) (hT₀ : Measurable T₀)
    (he : ∀ x, Z x ∈ B → T₀ (Z x) = h₀ x)
    (D : InitialWindowData β (μ.map Z) d T₀)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) :
    @IsChartMeanAt X mX β mβ μ Z B Y 0 𝒢₀
      (fun x => Aux61UnionK.canonMean.{v}
        (Aux61FibData.withQ d (D.correction (Z x))) (D.cutoff (Z x)) (ULift.up (Y x)) 0) := by
  apply Aux61GStep.isChartMeanAt_zero_of_initialData hZ hY hB D
  exact isChartGaussAt_of_mean_eqOn hY hB hG0
    (hT₀.comp (Measurable.of_comap_le hG0.marksZ)) he

end InteractingSLE.Sec5.Aux61GHist
