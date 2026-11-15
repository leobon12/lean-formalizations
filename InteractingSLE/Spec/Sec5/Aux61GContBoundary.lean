/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstRelativeBoundary

/-! # Reference germs, boundary cancellation, and measurable cuts

The hypotheses `hrelative` and `hreference_germ` are deliberately separate.
The former is the relative local-set comparison; the latter is the remaining
canonical height and inherited-phase calculation, including the seed.
These are conditional assembly results, not replacements of source theorems.
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

/-- Add the zero relative boundary limit to the reference-germ limit.
All derivative-lift and height offsets belong to the charted mean `M`. -/
theorem tendsto_sub_reference_of_relative {v M R : ℂ → ℝ} {a : ℝ}
    (hrelative : Tendsto (fun w => v w - M w) (𝓝[H] (a : ℂ)) (𝓝 0))
    (hreference_germ : Tendsto (fun w => M w - R w) (𝓝[H] (a : ℂ)) (𝓝 0)) :
    Tendsto (fun w => v w - R w) (𝓝[H] (a : ℂ)) (𝓝 0) := by
  have hadd := hrelative.add hreference_germ
  simpa only [sub_add_sub_cancel, add_zero] using hadd

/-- On a cover by seed and comparison patches, relative cancellation and
the exact reference germs give the boundary input for the correction. -/
theorem ae_boundary_of_relative_patches {β ι : Type*} [MeasurableSpace β]
    {μ : Measure β} (d : FibData) {T : β → DistOn upperHalfPlaneOpens}
    (O : ι → Set ℝ) (hO : d.O₀ ⊆ ⋃ j, O j) (M : ι → β → ℂ → ℝ)
    (hrelative : ∀ᵐ b ∂μ, ∀ j, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w) →
      ∀ a ∈ O j, Tendsto (fun w => v w - M j b w) (𝓝[H] (a : ℂ)) (𝓝 0))
    (hreference_germ : ∀ᵐ b ∂μ, ∀ j, ∀ a ∈ O j,
      Tendsto (fun w => M j b w - Aux61GlueK.refMean0 d w) (𝓝[H] (a : ℂ)) (𝓝 0)) :
    ∀ᵐ b ∂μ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w) →
      ∀ a ∈ d.O₀, Tendsto (fun w => v w - Aux61GlueK.refMean0 d w) (𝓝[H] (a : ℂ)) (𝓝 0) := by
  filter_upwards [hrelative, hreference_germ] with b hrel href
  intro v hv hrep a ha
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hO ha)
  exact tendsto_sub_reference_of_relative (hrel j v hv hrep a hj) (href j a hj)

/-- Complete the correction and cutoff selection from the two precisely
named boundary inputs. The initial-mean identity holds for every harmonic
representative; all histories have admissible corrections and cuts. -/
theorem exists_initialCorrection_cutoffs_of_relative {β ι : Type*} [MeasurableSpace β]
    {μ : Measure β} (d : FibData) {T : β → DistOn upperHalfPlaneOpens}
    (hT : Measurable T) (hh : ∀ᵐ b ∂μ, IsHarmonicDistOn (T b) H)
    (O : ι → Set ℝ) (hO : d.O₀ ⊆ ⋃ j, O j) (M : ι → β → ℂ → ℝ)
    (hrelative : ∀ᵐ b ∂μ, ∀ j, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w) →
      ∀ a ∈ O j, Tendsto (fun w => v w - M j b w) (𝓝[H] (a : ℂ)) (𝓝 0))
    (hreference_germ : ∀ᵐ b ∂μ, ∀ j, ∀ a ∈ O j,
      Tendsto (fun w => M j b w - Aux61GlueK.refMean0 d w) (𝓝[H] (a : ℂ)) (𝓝 0)) :
    ∃ (Q : β → ℂ → ℝ) (N : Set ℂ) (F : β → CMCut),
      Measurable (fun p : β × ℂ => Q p.1 p.2) ∧ (∀ b, ValidQ d (Q b)) ∧
      (∀ᵐ b ∂μ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
        (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w) →
        EqOn (Aux61GlueK.fibMean0 (withQ d (Q b))) v H) ∧
      d.buffer ⊆ N ∧ (∀ b, IsCutoffOn (F b) (withQ d (Q b)).q N d.O₀) ∧
      Measurable (fun p : β × ℂ => (withQ d (Q p.1)).q p.2) ∧
      Measurable (fun p : β × ℂ => (F p.1).f p.2) ∧
      Measurable (fun p : β × ℂ => QuantumZipper.K3.greenDensity (F p.1).f p.2) := by
  obtain ⟨Q, hQm, hQv, hrep⟩ := exists_measurable_validInitialCorrection d hT hh
    (ae_boundary_of_relative_patches d O hO M hrelative hreference_germ)
  obtain ⟨N, F, hbuf, hcut, hqm, hfm, hsrc⟩ := exists_measurable_fibreCutoffs d hQm hQv
  refine ⟨Q, N, F, hQm, hQv, ?_, hbuf, ?_, hqm, hfm, hsrc⟩
  · filter_upwards [hrep] with b hb
    intro v hv hvr w hw
    have hr : Aux61GlueK.refMean0 (withQ d (Q b)) w = Aux61GlueK.refMean0 d w := by
      unfold Aux61GlueK.refMean0
      rw [withQ_κ d (Q b), withQ_bR d (Q b), withQ_JR d (Q b)]
    rw [Aux61GlueK.fibMean0, hr, withQ_q_of_valid d (Q b) (hQv b)]
    exact hb v hv hvr hw
  · intro b
    simpa only [withQ_O₀] using hcut b

end InteractingSLE.Sec5.Aux61GCont
