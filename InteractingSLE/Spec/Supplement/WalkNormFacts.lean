/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkNormTrans
import InteractingSLE.Spec.Supplement.GW1PieceSimpleProof
import InteractingSLE.Spec.Supplement.GW3Sided

/-!
# Theorem 1.4's walk leaves: the almost sure path facts of the two walks

Packet PROVE-T14-WALKNORM. The pathwise geometry of the two walk leaves (`WalkNormChart`, `WalkNormPair`) uses facts
about the two boundary walks that the wiring of Theorem 1.4 already derives, independently of these leaves (R48:
Theorem 1.4 only):

* every piece launched by either walk is a simple piece of its launch chart meeting the old walk only at its seed
  (`GW1Z.GW1PieceSimpleStatement`, from GB6's restart, Theorem 1.3 and the launch clock);
* proper parametrizations of both walks and their common-contact order (`WalkInf.WalkPairPathFacts`, from
  `WalkCont.RightWalkProperRegStatement`, `GW3SidedProof.LeftWalkProperRegStatement` and
  `GW4BarrierSelf.WalkContactOrderRegStatement`);
* no nondegenerate common continuum (`WalkCont.WalkNoCommonContinuumRegStatement`);
* every between-component is a two-arc Jordan component or has an oriented uniformizer
  (`GW3Sided.GW3GeometryRegStatement`).

This file bundles them at one sample (`WalkPiecesSimple`, `WalkBetweenFacts`) and proves that they hold almost surely
under those statements (`ae_walkPiecesSimple`, `ae_walkBetweenFacts`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkNorm

open WalkInf WalkMean Exist.StagedLaw

/-- **Both walks have simple pieces at the sample `ω`** (the sample event of `GW1Z.GW1PieceSimpleStatement` for both
orientations). -/
def WalkPiecesSimple (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*}
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Prop :=
  ∀ (right : Bool) (k : ℕ) (c : Chart) (θ : ℝ),
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
      (k + 1)).2.2.2.1 k = some (c, θ) →
    GW1Z.IsSimplePiece c (E (GW1Z.walkSpec b jumps right) k ω).1
      (min (instrTime (GW1Z.walkSpec b jumps right) k) (E (GW1Z.walkSpec b jumps right) k ω).2)
      (SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω) k)

/-- **The path facts of the between-region at the sample `ω`**: the pair facts (proper parametrizations and contact
order), simple pieces, no nondegenerate common continuum, and the between-region geometry. -/
def WalkBetweenFacts (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*}
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Prop :=
  WalkPairPathFacts κ b jumps E ω ∧ WalkPiecesSimple κ b jumps E ω ∧
    (∀ S ⊆ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ∩
        ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω),
      IsPreconnected S → S.Subsingleton) ∧
    ∀ C ∈ betweenComponents
        (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
        (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)),
      GW3.IsTwoArcJordanComponent
          (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
          (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) C ∨
        GW3.HasOrientedUniformizer
          (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
          (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) C

section AE

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- Simple pieces of both walks, almost surely, from GW1's per-piece simplicity. -/
theorem ae_walkPiecesSimple (hS : GW1Z.GW1PieceSimpleStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hR : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hreg : ∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) :
    ∀ᵐ ω ∂P, WalkPiecesSimple κ b jumps E ω := by
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hR true,
    hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hR false] with ω h1 h2
  intro right
  cases right
  · exact h2
  · exact h1

/-- **The between-region path facts hold almost surely**, from the statements the wiring derives. -/
theorem ae_walkBetweenFacts (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hS : GW1Z.GW1PieceSimpleStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hG : GW3Sided.GW3GeometryRegStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hR : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hreg : ∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) :
    ∀ᵐ ω ∂P, WalkBetweenFacts κ b jumps E ω := by
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hCO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    ae_walkPiecesSimple hS hκ hκ4 hb hh hcf hζ' hE hR hreg,
    hNC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR] with ω h1 h2 h3 h4 h5 h6
  exact ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩

end AE

end InteractingSLE.Theorem14.WalkNorm
