/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GContBoundary

/-! # Constructed initial data for a fixed buffered reference window

`InitialWindowData` stores the correction and cuts already constructed by
the measurable harmonic-version and reflection theorems. Its existence
theorem states the still-required boundary identification explicitly.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.Aux61GCont
open Aux61GInst Aux61FibData
open Aux61Fib (FibData)
open Aux61Win (IsCutoffOn)
open Restart.FlowStopIdentCMI (CMCut)

universe u

/-- A history-dependent correction, its reflected cuts, and their
time-zero distributional identity for one fixed reference window. -/
structure InitialWindowData (β : Type*) [MeasurableSpace β]
    (μ : Measure β) (d : FibData) (T : β → DistOn upperHalfPlaneOpens) where
  correction : β → ℂ → ℝ
  correction_meas : Measurable (fun p : β × ℂ => correction p.1 p.2)
  valid : ∀ b, ValidQ d (correction b)
  represents : ∀ᵐ b ∂μ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
    (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w) →
    EqOn (Aux61GlueK.fibMean0 (withQ d (correction b))) v H
  neighbourhood : Set ℂ
  cutoff : β → CMCut
  buffer_sub : d.buffer ⊆ neighbourhood
  cut_on : ∀ b, IsCutoffOn (cutoff b) (withQ d (correction b)).q neighbourhood d.O₀
  q_meas : Measurable (fun p : β × ℂ => (withQ d (correction p.1)).q p.2)
  cut_meas : Measurable (fun p : β × ℂ => (cutoff p.1).f p.2)
  source_meas : Measurable (fun p : β × ℂ => QuantumZipper.K3.greenDensity (cutoff p.1).f p.2)

/-- The selected cutoffs retain the actual time-zero mean, simultaneously
for every decoded path and every harmonic representative. -/
theorem InitialWindowData.ae_canonMean_zero_eq {β : Type*} [MeasurableSpace β]
    {μ : Measure β} {d : FibData} {T : β → DistOn upperHalfPlaneOpens}
    (D : InitialWindowData β μ d T) :
    ∀ᵐ b ∂μ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w) →
      ∀ s : ULift.{u} Aux61Fib.FibCode,
      EqOn (Aux61UnionK.canonMean (withQ d (D.correction b)) (D.cutoff b) s 0) v H := by
  filter_upwards [D.represents] with b hb
  intro v hv hrep s
  exact (canonMean_zero _ _ s).trans (hb v hv hrep)

/-- A measurable harmonic initial distribution admits all the window data
once its actual boundary values agree with the reference mean, including
the seed. This is the exact named remaining mathematical input. -/
theorem nonempty_initialWindowData {β : Type*} [MeasurableSpace β]
    {μ : Measure β} (d : FibData) {T : β → DistOn upperHalfPlaneOpens}
    (hT : Measurable T) (hh : ∀ᵐ b ∂μ, IsHarmonicDistOn (T b) H)
    (hboundary_identification : ∀ᵐ b ∂μ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w) →
      ∀ a ∈ d.O₀, Tendsto (fun w => v w - Aux61GlueK.refMean0 d w) (𝓝[H] (a : ℂ)) (𝓝 0)) :
    Nonempty (InitialWindowData β μ d T) := by
  have hO : d.O₀ ⊆ ⋃ _ : Unit, d.O₀ := by simp only [iUnion_const, subset_refl]
  have hreference : ∀ᵐ b ∂μ, ∀ _ : Unit, ∀ a ∈ d.O₀,
      Tendsto (fun w => Aux61GlueK.refMean0 d w - Aux61GlueK.refMean0 d w)
        (𝓝[H] (a : ℂ)) (𝓝 0) := by
    filter_upwards [] with b
    intro j a ha
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℂ => (0 : ℝ)) (𝓝[H] (a : ℂ)) (𝓝 0))
  have hrelative : ∀ᵐ b ∂μ, ∀ _ : Unit, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w) →
      ∀ a ∈ d.O₀, Tendsto (fun w => v w - Aux61GlueK.refMean0 d w) (𝓝[H] (a : ℂ)) (𝓝 0) :=
    hboundary_identification.mono fun b hb _ => hb
  obtain ⟨Q, N, F, hQm, hQv, hrep, hbuf, hcut, hqm, hfm, hsrc⟩ :=
    exists_initialCorrection_cutoffs_of_relative d hT hh (fun _ : Unit => d.O₀) hO
      (fun _ _ => Aux61GlueK.refMean0 d) hrelative hreference
  exact ⟨⟨Q, hQm, hQv, hrep, N, F, hbuf, hcut, hqm, hfm, hsrc⟩⟩

end InteractingSLE.Sec5.Aux61GCont
