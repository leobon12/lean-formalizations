/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GContData
import InteractingSLE.Spec.Sec5.Aux61OldBKB

/-! # Time-zero mean identification from the constructed initial data

The stored representative identity pulls back from the retained-history
law. The actual Gaussian decomposition supplies a harmonic representative;
uniqueness then gives (K-b) for every decomposition at time zero.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GStep
open Aux61GCont Aux61FibData
open Aux61Fib (FibData FibCode)
open Aux61ChLoc (IsChartGaussAt IsChartMeanAt)
open Aux61UnionK (canonMean chartHull)

universe u v
variable {X : Type u} {𝒢₀ : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [MeasurableSpace β]
  {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode}
  {d : FibData} {T₀ : β → DistOn upperHalfPlaneOpens}

/-- Constructed initial data represent the actual retained-history
harmonic distribution, almost surely on the live event. -/
theorem ae_initial_pairing (hZ : Measurable Z)
    (D : InitialWindowData β (μ.map Z) d T₀)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ (fun x => T₀ (Z x))) :
    ∀ᵐ x ∂μ, Z x ∈ B → ((0 : ℝ≥0) : ℝ≥0∞) < (Y x).life →
      ∀ ψ : TestOn upperHalfPlaneOpens, T₀ (Z x) ψ =
        ∫ z, Aux61GlueK.fibMean0 (withQ d (D.correction (Z x))) z * ψ z := by
  filter_upwards [ae_of_ae_map hZ.aemeasurable D.represents, hG0.harmonic] with x hx hh hxB hlt
  have hhH : IsHarmonicDistOn (T₀ (Z x)) H := by
    simpa only [Aux61OldB.chartHull_zero, sdiff_empty] using hh hxB hlt
  obtain ⟨v, hv, hrep⟩ := hhH
  have he := hx v hv (fun ψ => hrep ψ ψ.tsupport_subset)
  intro ψ
  rw [hrep ψ ψ.tsupport_subset]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  by_cases hz : z ∈ H
  · rw [he hz]
  · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun hm => hz (ψ.tsupport_subset hm)
    simp only [h0, mul_zero]

/-- The initial-data construction discharges the time-zero (K-b) premise
of the old-boundary positive-time mean theorem. -/
theorem isChartMeanAt_zero_of_initialData [IsFiniteMeasure μ]
    (hZ : Measurable Z) (hY : Measurable Y) (hB : MeasurableSet B)
    (D : InitialWindowData β (μ.map Z) d T₀)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ (fun x => T₀ (Z x))) :
    @IsChartMeanAt X mX β _ μ Z B Y 0 𝒢₀
      (fun x => canonMean.{v} (withQ d (D.correction (Z x))) (D.cutoff (Z x)) (ULift.up (Y x)) 0) := by
  exact Aux61OldB.isChartMeanAt_zero_of_fibMean0 hY hB hG0 (ae_initial_pairing hZ D hG0)

end InteractingSLE.Sec5.Aux61GStep
