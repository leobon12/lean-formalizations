/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KcChart

/-!
# SB2(1)'s measurable launch chart and countable force-word partition

This combines the existing measurable entry and chart construction with the
countable-profile stage witness. It supplies the chart, conditional field, and
countable force types for K2 at every launch after the first. The relative
driver, marked union kernels, and lifetime reconstruction are separate proof
obligations; this file asserts none of them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw WalkInf Supp8.Q3Stop

/-- The previously constructed launch chart and entry can use a conditional
word with countably many force types, without an active-word premise. -/
theorem exists_k2Launch_countable_types {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {w : ExplSpec}
    (hw : w = boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (hS : IsStagedHistory κ b jumps P h w (E w))
    (hR : StagedPiecesRegular κ b jumps P w (E w))
    (hreg : ∀ j ω, IsRegularDriver (E w j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps →
      b t + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (k : ℕ) (θ : ℝ) {u : ℝ} (hu : u ≤ 0) :
    ∃ (m : Ω → ℝ) (cw : Ω → Restart.BoundaryWord) (T : Set WordType),
      Measurable[pastSigma κ b jumps w (E w) (k + 1)] m ∧
      Measurable[pastSigma κ b jumps w (E w) (k + 1)] cw ∧
      IsMeasChart (pastSigma κ b jumps w (E w) (k + 1))
        (fun ω => (verChart κ b jumps w (E w) (k + 1) ω).recenter (m ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
        (verChart κ b jumps w (E w) (k + 1) ω).recenter (m ω) =
          (launchChart κ b jumps E (k + 1) ω).recenter
            (launchEntry κ b jumps E (k + 1) u ω)) ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
        IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
        ∃ h' : Ω → DistOn upperHalfPlaneOpens,
          (∀ ω, IsChartTransport
            ((verChart κ b jumps w (E w) (k + 1) ω₀).recenter (m ω₀))
            1 0 (chiC κ) (h ω) (h' ω)) ∧
          IsGFFWithBoundaryData
            (condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀)
            h' (cw ω₀).fn (cw ω₀).jumps) ∧
      (∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P
        (pastSigma κ b jumps w (E w) (k + 1)) ω₀),
        (verChart κ b jumps w (E w) (k + 1) ω).recenter (m ω) =
          (verChart κ b jumps w (E w) (k + 1) ω₀).recenter (m ω₀)) ∧
      T.Countable ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → angleWordType κ θ (cw ω) ∈ T := by
  subst hw
  obtain ⟨m, _, hm, _, hmc, heq, _, hcc⟩ :=
    exists_k2ChartInputs_launch_succ hκ hb hh rfl hS hR hreg hamb k hu
  obtain ⟨cw, T, hcw, hT, hcover, hG⟩ :=
    exists_k2Word_countable_types hκ hb hh hS hR hreg (k + 1) θ hm
  exact ⟨m, cw, T, hm, hcw, hmc, heq, hG, hcc, hT, hcover⟩

end InteractingSLE.Theorem14.SB.Lv
