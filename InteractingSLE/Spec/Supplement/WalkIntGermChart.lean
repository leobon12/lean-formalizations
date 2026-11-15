/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntGermWord
import InteractingSLE.Spec.Supplement.WalkIntBridgeChart

/-!
# GW3 conditional on the remaining incident boundary geometry

This named mathematical input supplies the exact finite word and incident
boundary correspondences. It supplies no lift comparisons or integers.
The original chart leaves follow through the landed Bridge consumers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkIntGerm

open WalkMean WalkBdry WalkNorm

/-- Exact remaining GW3 geometry. The predicates contain incident real
intervals and raw collar data, but no boundary lift comparison or integer. -/
def WalkIncidentGeometryStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkBetweenFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ C ∈ betweenComponents
        (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
        (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2),
        ∃ (t : Chart × (ℝ → ℝ) × Finset ℝ) (F : IncidentHullFamily t.1),
          IsNormChartIncident κ b jumps (walkRuns κ b jumps E ω) C t F

/-- All inherited-lift requirements of the earlier named reference input
follow from incident geometry. -/
theorem walkReferenceGeometryStatement_of_incident
    (hgeom : WalkIncidentGeometryStatement.{u}) :
    WalkIntBridge.WalkReferenceGeometryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  filter_upwards [hgeom κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts,
    hfacts] with ω hω hf C hC
  obtain ⟨t, F, ht⟩ := hω C hC
  have hCoH : IsOpen C ∧ C ⊆ H := by
    rcases hf.2.2.2 C hC with hJ | hU
    · exact ⟨hJ.1, hJ.2.2.1⟩
    · exact ⟨hU.1, hU.2.1⟩
  obtain ⟨hc, -⟩ := WalkIntBridge.hasDerivLift_of_isComponentChart ht.1 hCoH.1 hCoH.2
  exact ⟨t, F.referenceFamily hc, isNormChartRef_of_incident hc ht⟩

theorem walkNormChartLocStatement_of_incidentGeometry
    (hgeom : WalkIncidentGeometryStatement.{u}) : WalkNormChartLocStatement.{u} :=
  WalkIntBridge.walkNormChartLocStatement_of_referenceGeometry
    (walkReferenceGeometryStatement_of_incident hgeom)

theorem walkNormChartStatement_of_incidentGeometry
    (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hS : GW1Z.GW1PieceSimpleStatement.{u})
    (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hG : GW3Sided.GW3GeometryRegStatement.{u})
    (hgeom : WalkIncidentGeometryStatement.{u}) : WalkNormChartStatement.{u} :=
  WalkIntBridge.walkNormChartStatement_of_referenceGeometry hPR hPL hCO hS hNC hG
    (walkReferenceGeometryStatement_of_incident hgeom)

end InteractingSLE.Theorem14.WalkIntGerm
