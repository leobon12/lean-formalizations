/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GVanMap
import InteractingSLE.Spec.Sec5.Aux61GInstData

/-! # Transfer the actual representative boundary comparison to history

Choose the existing jointly measurable harmonic correction. Its boundary
event is measurable by the compact-patch criterion. Pull the actual
representative comparison to this correction, transfer its vanishing to
the history law, then recover every harmonic representative there.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.Aux61GVan
open Aux61Fib (FibData)

/-- A physical-space boundary comparison for the actual factored mean
gives the corresponding assertion for every representative under the
retained-history law. The boundary-event measurability is proved here. -/
theorem ae_boundary_identification_of_pullback
    {X β : Type*} [MeasurableSpace X] [MeasurableSpace β]
    {μ : Measure X} {Z : X → β} (hZ : Measurable Z) {B : Set β} (hB : MeasurableSet B)
    (d : FibData) {T₀ : β → DistOn upperHalfPlaneOpens} (hT₀ : Measurable T₀)
    (hharm : ∀ᵐ b ∂μ.map Z, IsHarmonicDistOn (T₀ b) H)
    (hphysical_boundary : ∀ᵐ x ∂μ, Z x ∈ B → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T₀ (Z x) ψ = ∫ z, v z * ψ z) →
      ∀ a ∈ d.O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 d z)
        (𝓝[H] (a : ℂ)) (𝓝 0)) :
    ∀ᵐ b ∂μ.map Z, b ∈ B → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T₀ b ψ = ∫ z, v z * ψ z) →
      ∀ a ∈ d.O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 d z)
        (𝓝[H] (a : ℂ)) (𝓝 0) := by
  obtain ⟨Q, hQm, hQh, hQrep⟩ := Aux61GInst.exists_measurable_initialCorrection d hT₀ hharm
  have hQpoint : ∀ z ∈ H, Measurable (fun b => Q b z) :=
    fun z _ => hQm.comp (measurable_id.prodMk measurable_const)
  have hQc : ∀ b, ContinuousOn (Q b) H :=
    fun b z hz => ((hQh b) z hz).1.continuousAt.continuousWithinAt
  have hQpull : ∀ᵐ x ∂μ, Z x ∈ B → ∀ a ∈ d.O₀,
      Tendsto (Q (Z x)) (𝓝[H] (a : ℂ)) (𝓝 0) := by
    filter_upwards [ae_of_ae_map hZ.aemeasurable hharm,
      ae_of_ae_map hZ.aemeasurable hQrep, hphysical_boundary] with x hxH hxrep hxphys hxB
    obtain ⟨v, hv, hrep⟩ := hxH
    have hp : ∀ ψ : TestOn upperHalfPlaneOpens, T₀ (Z x) ψ = ∫ z, v z * ψ z :=
      fun ψ => hrep ψ ψ.tsupport_subset
    intro a ha
    apply (hxphys hxB v hv hp a ha).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have he := hxrep v hv hp hz
    dsimp only at he ⊢
    linarith only [he]
  have hH : H.Nonempty := ⟨Complex.I, by simp only [H, mem_ofPred_eq, Complex.I_im, zero_lt_one]⟩
  have hQzero := (ae_boundary_zero_map_iff hZ hB hH d.O₀_open hQpoint hQc).2 hQpull
  filter_upwards [hQrep, hQzero] with b hb hzero hbB
  intro v hv hrep a ha
  apply (hzero hbB a ha).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he := hb v hv hrep hz
  dsimp only at he ⊢
  linarith only [he]

end InteractingSLE.Sec5.Aux61GVan
