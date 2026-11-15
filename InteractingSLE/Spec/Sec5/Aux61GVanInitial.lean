/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GVanTransfer
import InteractingSLE.Spec.Sec5.Aux61GHistInitial

/-! # Correction and cutoff selection from physical-space boundary data

The actual boundary comparison may be established on the original sample
space, localized to the chosen history event. It now gives initial window
data on the history space without a separate image-law boundary hypothesis.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.Aux61GVan
open Aux61Fib (FibData)
open Aux61GCont (InitialWindowData)
open Aux61FibData

/-- Constructed initial data recover their reference boundary comparison
for every harmonic representative, almost surely. -/
theorem ae_boundary_identification_of_initialData {β : Type*} [MeasurableSpace β]
    {ν : Measure β} {d : FibData} {T₀ : β → DistOn upperHalfPlaneOpens}
    (D : InitialWindowData β ν d T₀) :
    ∀ᵐ b ∂ν, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T₀ b ψ = ∫ z, v z * ψ z) →
      ∀ a ∈ d.O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 d z)
        (𝓝[H] (a : ℂ)) (𝓝 0) := by
  filter_upwards [D.represents] with b hb
  intro v hv hrep a ha
  apply ((D.valid b).2 a ha).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he := hb v hv hrep hz
  have hr : Aux61GlueK.refMean0 (withQ d (D.correction b)) z = Aux61GlueK.refMean0 d z := by
    unfold Aux61GlueK.refMean0
    rw [withQ_κ, withQ_bR, withQ_JR]
  rw [Aux61GlueK.fibMean0, hr, withQ_q_of_valid d (D.correction b) (D.valid b)] at he
  linarith only [he]

/-- The actual physical initial mean supplies history-space correction
and cutoff data once its on-event boundary comparison is known. -/
theorem nonempty_initialWindowData_of_actual_boundary
    {X β : Type*} [MeasurableSpace X] [MeasurableSpace β]
    {μ : Measure X} {Z : X → β} (hZ : Measurable Z) {B : Set β} (hB : MeasurableSet B)
    (d : FibData) {T₀ : β → DistOn upperHalfPlaneOpens} (hT₀ : Measurable T₀)
    (hharm : ∀ᵐ b ∂μ.map Z, IsHarmonicDistOn (T₀ b) H)
    (hoff : ∀ b ∉ B, T₀ b = Aux61GHist.referenceDist d)
    {h₀ : X → DistOn upperHalfPlaneOpens} (he : ∀ x, Z x ∈ B → T₀ (Z x) = h₀ x)
    (hphysical_boundary : ∀ᵐ x ∂μ, Z x ∈ B → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, h₀ x ψ = ∫ z, v z * ψ z) →
      ∀ a ∈ d.O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 d z)
        (𝓝[H] (a : ℂ)) (𝓝 0)) :
    Nonempty (InitialWindowData β (μ.map Z) d T₀) := by
  apply Aux61GHist.nonempty_initialWindowData_of_local_history_boundary d hT₀ hharm hoff
  apply ae_boundary_identification_of_pullback hZ hB d hT₀ hharm
  filter_upwards [hphysical_boundary] with x hx hxB
  intro v hv hp
  exact hx hxB v hv (by simpa only [he x hxB] using hp)

/-- Initial data constructed on the localized physical sample space can
be reconstructed measurably on the retained-history space. The physical
cutoffs themselves need not be measurable functions of that history. -/
theorem nonempty_initialWindowData_of_restricted_initialData
    {X β : Type*} [MeasurableSpace X] [MeasurableSpace β]
    {μ : Measure X} {Z : X → β} (hZ : Measurable Z) {B : Set β} (hB : MeasurableSet B)
    (d : FibData) {T₀ : β → DistOn upperHalfPlaneOpens} (hT₀ : Measurable T₀)
    (hharm : ∀ᵐ b ∂μ.map Z, IsHarmonicDistOn (T₀ b) H)
    (hoff : ∀ b ∉ B, T₀ b = Aux61GHist.referenceDist d)
    {h₀ : X → DistOn upperHalfPlaneOpens} (he : ∀ x, Z x ∈ B → T₀ (Z x) = h₀ x)
    (Dphys : InitialWindowData X (μ.restrict (Z ⁻¹' B)) d h₀) :
    Nonempty (InitialWindowData β (μ.map Z) d T₀) := by
  apply nonempty_initialWindowData_of_actual_boundary hZ hB d hT₀ hharm hoff he
  exact (ae_restrict_iff' (hB.preimage hZ)).1 (ae_boundary_identification_of_initialData Dphys)

end InteractingSLE.Sec5.Aux61GVan
