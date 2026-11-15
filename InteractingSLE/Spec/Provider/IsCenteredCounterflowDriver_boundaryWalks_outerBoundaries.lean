import InteractingSLE.Spec.AuditFix.FrontierBridge

/-!
# Provider for a frozen anchor (sealed)

Anchor file: `InteractingSLE/Frozen/Spec/IsCenteredCounterflowDriver_boundaryWalks_outerBoundaries.lean`.

The statement is the frozen anchor's; the proof is the closed theorem
`InteractingSLE.AuditFix.frontierNowhereFilling_holds` (external-audit response, ruling R122).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Spec.Provider

theorem IsCenteredCounterflowDriver_boundaryWalks_outerBoundaries :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
      ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
      ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
        (∀ᵐ ω ∂P, ζ' ω = ⊤) →
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        ∀ᵐ ω ∂P,
          let K := counterflowCompletedRange (fun t => W' t ω)
          let R := ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
          let L := ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
          interior (((↑) : ℝ → ℂ) ⁻¹' K) = ∅ →
            ((E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
              (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤) ∧
            (R = {0} ∪ Chart.id.tipSet (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).1 ⊤ ∧
              L = {0} ∪ Chart.id.tipSet (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).1 ⊤) ∧
            (R = frontier (rightSideOf K) ∩ K ∧ L = frontier (leftSideOf K) ∩ K) ∧
            (R = closure (frontier (rightSideOf K) ∩ QuantumZipper.H) ∧
              L = closure (frontier (leftSideOf K) ∩ QuantumZipper.H)) ∧
            (R ∪ L = frontier (rightSideOf K ∪ leftSideOf K) ∩ K ∧
              R ∪ L = closure (frontier (rightSideOf K ∪ leftSideOf K) ∩ QuantumZipper.H)) :=
  by exact InteractingSLE.AuditFix.frontierNowhereFilling_holds

end InteractingSLE.Spec.Provider
