/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3SidedProofWalk

/-!
# Theorem 1.4's component kernels, version 2: the wiring from the walk inputs

Packet PROVE-T14-GW8. The version-2 component-kernel anchor (R51) in provider shape from the finest named inputs now
left: the proper parametrizations of the two walks, GW2a's containment, SB's frontier statement, the sides of the real
connectors, the piece statement, the marked union law of the walks, GW4's traversal core and Theorems 1.2–1.3. Lemma
GW3's geometry comes from `GW3SidedProof.gw3GeometryRegStatement_of_walks` (no sided-geometry input is left), the
field law from the union law (`GW3Joint`), the word bounds, kernels and assembly from `GW4R51`. Conditional helper;
not the provider.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW4R51

/-- **Theorem 1.4, component kernels, version 2** (R51), provider shape, from the walk inputs: both walks proper curves
from `0`, GW2a's containment, SB's frontier statement (regular families), the sides of the real connectors, the piece
statement, the marked union law, GW4's traversal core (R51 form) and Theorems 1.2–1.3 (conditional helper; not the
provider). -/
theorem componentKernels_of_walkInputs (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hS : WalkCont.WalkConnectorSideRegStatement.{u})
    (hNP : WalkCont.WalkPieceContinuumRegStatement.{u}) (hU : GW3Joint.GW3UnionLawRegStatement.{u})
    (hT : GW4TraversalCoreRegStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption)
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec) := by assumption) :
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν := by
  have hG := GW3SidedProof.gw3GeometryRegStatement_of_walks hPR hPL hA hF
    (GW3SidedProof.rightWalkNegRealRegStatement_of_pieces hPR hS hNP)
  have hO := GW3Sided.betweenComponentsOpenRegStatement_of_geometry hG
  exact componentKernels_of_regKernels (GW3Sided.gw3ChartRegStatement_of_geometry hG)
    (gw4KernelRegStatement_of_thm12
      (GW3Joint.gw3FieldLawRegStatement_of_oneChart hO (WalkCont.walkNoCommonContinuumRegStatement_of_pieces hPR hS hNP)
        (GW3Joint.gw3FieldLawOneChartRegStatement_of_unionLaw hU))
      (gw4TraversalRegStatement_of_core hT
        (gw3WordBoundRegStatement_of_inputs hO (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hS)) h12 h13)
    hκ hκ4 hb hh hcf hζ' hE hreg

end InteractingSLE.Theorem14.GW4R51
