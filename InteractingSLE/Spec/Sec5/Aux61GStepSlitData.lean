/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GStepMean

/-! # The glued sample's cutoff fields follow from initial data

Only the physical slit geometry and marked smaller-mean comparison remain
in this constructor. The correction, parameter, cut and hull buffer fields
are supplied by the constructed initial data and the code's path facts.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Metric
open QuantumZipper (H fwdHull fwdMapInv)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GStep
open Aux61GCont Aux61FibData
open Aux61Fib (FibData FibCode PathGood)
open Aux61Conf2 (IsGluedSlit IsGluedSlitSample)

/-- Construct the precise glued sample consumed by the positive-time mean
identification. Its analytic cutoff fields need no additional assumptions. -/
theorem gluedSlitSample_of_initialData {β : Type*} [MeasurableSpace β]
    {ν : Measure β} {d : FibData} {T₀ : β → DistOn upperHalfPlaneOpens}
    (D : InitialWindowData β ν d T₀) (b : β) {s : FibCode} {q : ℝ≥0}
    (hgood : PathGood d s) (hq : (q : ℝ≥0∞) < s.life)
    {Wph : ℝ → ℝ} {η γ : ℝ → ℂ} {r τ Tc : ℝ} {c : Chart} {Ω : Set ℂ}
    (hglued : IsGluedSlit Wph η r τ c Ω (fun t : ℝ => s.driver t.toNNReal) γ Tc q)
    {J : Type*} {ρ : J → ℝ} {L : J → Set ℂ} {A : Set ℂ} {M₂ uph : J → ℂ → ℝ}
    (hcover : ∀ u ∈ Ioo 0 τ, ∃ j, r + u < ρ j ∧ ρ j < r + τ ∧ η (r + u) ∈ L j ∧
      ∃ ε > 0, A ∩ ball (η (r + u)) ε ⊆ L j)
    (hmean : ∀ j, ∀ z ∈ Ω, M₂ j z = couplingMean d.κ Wph (ρ j) (uph j) z)
    (hphysL : ∀ j, ∀ p : ℝ, p < 0 → extendFrom H (fwdMapInv Wph (ρ j)) p ∈ H →
      Tendsto (uph j) (𝓝[H] (p : ℂ)) (𝓝 (-(Real.pi / Real.sqrt d.κ))))
    (hphysR : ∀ j, ∀ p : ℝ, 0 < p → extendFrom H (fwdMapInv Wph (ρ j)) p ∈ H →
      Tendsto (uph j) (𝓝[H] (p : ℂ)) (𝓝 (Real.pi / Real.sqrt d.κ))) :
    IsGluedSlitSample d.κ (withQ d (D.correction b)) (D.cutoff b) D.neighbourhood s q
      Wph η r τ c Ω γ Tc ρ L A M₂ uph := by
  refine ⟨hglued, withQ_κ d (D.correction b), ?_, ?_, hcover, hmean, hphysL, hphysR⟩
  · simpa only [withQ_O₀] using D.cut_on b
  · exact (Aux61GlueK.closure_fwdHull_subset_buffer hgood hq).trans D.buffer_sub

end InteractingSLE.Sec5.Aux61GStep
