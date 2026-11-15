/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkPieceProof
import InteractingSLE.Spec.Supplement.WalkProper
import InteractingSLE.Spec.Supplement.GW4R51Wire

/-!
# Theorem 1.4's component kernels, version 2: the wiring from the finer walk inputs

Packet PROVE-T14-GW9. PROVE-T14-GW8's `GW4R51.componentKernels_of_walkInputs` with two inputs discharged:

* the piece statement `WalkCont.WalkPieceContinuumRegStatement` is replaced by its clause (1) alone
  (`WalkPiece.WalkPiecePairRegStatement`); clauses (2)–(3) follow from the walks' proper parametrizations by Lemma 2.5
  (`WalkPiece.walkPieceContinuumRegStatement_of_pair`);
* the sides of the real connectors come from Theorem 1.3 (`GW1X.walkConnectorSideRegStatement_of_theorem13`).

`componentKernels_of_walkCores` further takes the walks' parametrizations in their every-sample-regular forms
(`GW1X.GW1ParamEveryRegStatement`, `WalkProper.LeftWalkParamEveryRegStatement`). Conditional helpers; not the provider.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.WalkPiece

/-- **Theorem 1.4, component kernels, version 2** (R51), provider shape, from: both walks proper curves from `0`,
GW2a's containment, SB's frontier statement, clause (1) of the piece statement, the marked union law, GW4's traversal
core (R51 form) and Theorems 1.2–1.3 (conditional helper; not the provider). -/
theorem componentKernels_of_walkPair (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hpair : WalkPiecePairRegStatement.{u})
    (hU : GW3Joint.GW3UnionLawRegStatement.{u}) (hT : GW4R51.GW4TraversalCoreRegStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
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
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  GW4R51.componentKernels_of_walkInputs hPR hPL hA hF (GW1X.walkConnectorSideRegStatement_of_theorem13 h13₀)
    (walkPieceContinuumRegStatement_of_pair hPR hPL hpair) hU hT h12 h13 h13₀

/-- **Theorem 1.4, component kernels, version 2** (R51), provider shape, from the walks' parametrizations for families
regular at every sample (GW1's simple-curve core for each walk), GW2a's containment, SB's frontier statement, clause (1)
of the piece statement, the marked union law, GW4's traversal core and Theorems 1.2–1.3 (conditional helper; not the
provider). -/
theorem componentKernels_of_walkCores (hGR : GW1X.GW1ParamEveryRegStatement.{u})
    (hGL : WalkProper.LeftWalkParamEveryRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hpair : WalkPiecePairRegStatement.{u})
    (hU : GW3Joint.GW3UnionLawRegStatement.{u}) (hT : GW4R51.GW4TraversalCoreRegStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
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
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  componentKernels_of_walkPair
    (GW1X.rightWalkProperRegStatement_of_gw1ParamR51 (GW1X.gw1ParamR51Statement_of_everyReg hGR))
    (WalkProper.leftWalkProperRegStatement_of_everyReg hGL) hA hF hpair hU hT h12 h13 h13₀

end InteractingSLE.Theorem14.WalkPiece
