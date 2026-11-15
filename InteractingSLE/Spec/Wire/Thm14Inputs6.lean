/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm14InputsR51
import InteractingSLE.Spec.Supplement.GW2ConeQ
import InteractingSLE.Spec.Supplement.GW2TipAssembly
import InteractingSLE.Spec.Supplement.SB4Clauses
import InteractingSLE.Spec.Supplement.GW3UnionLawProofWire
import InteractingSLE.Spec.Supplement.GW4BarrierCondWire
import InteractingSLE.Spec.Supplement.WalkPastDet

/-!
# Theorem 1.4 wires from the latest remaining inputs

The light cone uses GB9a's schedule set and derives the all-schedule-set exhaustion from TIP9's joint-chart
unboundedness input. The frontier wrapper uses SB4's regularized clauses. The component-kernel wrapper uses the
between-component union law and builds the retained-past determination and GW4 traversal core from their current finer
inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- Theorem 1.4's light-cone anchor on the interior schedule-set route. -/
theorem completedRange_eq_closure_lightCone_of_wire6
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0})
    (hBR6 : Theorem14.BR6.BR6Statement.{u}) (hBR4a : Theorem14.BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : Theorem14.GW2Later.GB6PrefixPairStatement.{u})
    (hQ : Theorem14.GW2Tip.GW2InteriorScheduleQStatement.{u})
    (hU : Theorem14.GW2Tip.GW2TipJointUnboundedStatement.{u})
    (hGW2a : Theorem14.GW2aContainmentStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption)
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {Θ : Set ℝ} (hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by assumption)
    (hΘc : Θ.Countable := by assumption)
    (hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ := by assumption) :
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        (∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
            counterflowCompletedRange (fun t => W' t ω)) ∧
        ∀ 𝒞 : Set (List Instr), 𝒞.Countable → (∀ p ∈ 𝒞, IsBoundaryContinuedProgram p) →
          ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪
              (⋃ p ∈ 𝒞, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω)) ∪
              {0}) =
            counterflowCompletedRange (fun t => W' t ω) :=
  let hExCanon := Theorem14.GW2Tip.gw2TipExhaustionCanonAllQStatement_of_jointUnbounded hU
  let hEx := Theorem14.GW2Tip.gw2TipExhaustionAllQStatement_of_canonAllQ h12 h13 hExCanon
  Theorem14.GW2Tip.completedRange_eq_closure_lightCone_of_interiorQ h13 h13₀ hBR6 hBR4a hGB6 hG hQ hEx hGW2a
    hκ hκ4 hb hh hcf hζ' hΘ hΘc hΘd

/-- Theorem 1.4's frontiers from the regularized SB4 clauses. -/
theorem boundaryWalks_frontiers_of_wire6 (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : Theorem14.BR6.BR6Statement.{u})
    (hC0 : Theorem14.GW2Cone.GW2ScheduleContainmentStatement.{u})
    (hCv : Theorem14.GW2Cone.GW2ArcScheduleContainmentStatement.{u})
    (hEx : Theorem14.GW2Cone.GW2TipExhaustionStatement.{u})
    (hGW2a : Theorem14.GW2aContainmentStatement.{u})
    (hDS : Theorem14.SB.SB4DistinctSeedRegStatement.{u})
    (hIA : Theorem14.SB.SB4InitialArcRegStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption)
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption)
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec) := by assumption) :
    ∀ᵐ ω ∂P,
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅) ∧
      (interior (((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω)) = ∅ →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
          (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤) :=
  Theorem14.SB.boundaryWalks_frontiers_of_openReg2 h13 h13₀ hBR6 hC0 hCv hEx hGW2a hDS hIA
    hκ hκ4 hb hh hcf hζ' hE hreg

/-- Theorem 1.4's component kernels from the between-component walk laws and the finer GW4 inputs. -/
theorem componentKernels_of_wire6
    (hGR : Theorem14.GW1X.GW1ParamEveryRegStatement.{u})
    (hGL : Theorem14.WalkProper.LeftWalkParamEveryRegStatement.{u})
    (hA : Theorem14.GW2aContainmentStatement.{u}) (hF : Theorem14.SB.SBFrontierRegStatement.{u})
    (hpair : Theorem14.WalkPiece.WalkPiecePairRegStatement.{u})
    (hR : Theorem14.WalkLaw.WalkMarkedLocalRegStatement.{u} (-(Real.pi / 2)) true)
    (hWalkL : Theorem14.WalkLaw.WalkMarkedLocalRegStatement.{u} (Real.pi / 2) false)
    (hM : Theorem14.WalkLaw.WalkUnionMeanRegStatement.{u})
    (hG : Theorem14.GW4Reg.GB11RelConnGrowthStatement)
    (hB : Theorem14.GW4Reg.GW4BarrierSelfRegStatement.{u})
    (hLaw : Theorem14.GW4Reg.GW4RelativeLawRegStatement.{u})
    (hNR : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption)
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
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
  let hPR := Theorem14.GW1X.rightWalkProperRegStatement_of_gw1ParamR51
    (Theorem14.GW1X.gw1ParamR51Statement_of_everyReg hGR)
  let hPL := Theorem14.WalkProper.leftWalkProperRegStatement_of_everyReg hGL
  let hS := Theorem14.GW1X.walkConnectorSideRegStatement_of_theorem13 h13₀
  let hNP := Theorem14.WalkPiece.walkPieceContinuumRegStatement_of_pair hPR hPL hpair
  let hGeom := Theorem14.GW3SidedProof.gw3GeometryRegStatement_of_walks hPR hPL hA hF
    (Theorem14.GW3SidedProof.rightWalkNegRealRegStatement_of_pieces hPR hS hNP)
  let hO := Theorem14.GW3Sided.betweenComponentsOpenRegStatement_of_geometry hGeom
  let hWB := Theorem14.GW4R51.gw3WordBoundRegStatement_of_inputs hO
    (Theorem14.BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hS
  let hT := Theorem14.GW4Reg.gw4TraversalCoreRegStatement_of_connGrowthSelf
    h12 h13 hO hWB hG hB hLaw hNR
  let hdet := Theorem14.WalkLaw.pastDetRegStatement_of_thm12_thm13
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
  exact Theorem14.GW3Between.componentKernels_of_walkLaws
    hGR hGL hA hF hpair hdet hR hWalkL hM hT h12 h13 h13₀
    hκ hκ4 hb hh hcf hζ' hE hreg

/-- The companion of Theorem 1.4. -/
theorem exists_isStagedHistory_of_wire6 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec) ∧ StagedPiecesRegular κ b jumps P spec (E spec) :=
  exists_isStagedHistory_of_openR51 h12 h13 hκ hκ4 hb hh

end Wire

end InteractingSLE
