/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFiberWord

/-!
# GW3 reduced to physical retained-boundary and side geometry

Proper finite charts and their physical boundary landings construct all
real transition intervals. The finite word and central designated incident
coordinates remain named mathematical inputs, with the source leaves intact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkIntFiber

open WalkMean WalkBdry WalkNorm

/-- Exact remaining geometry: physical retained-boundary intervals, the
finite boundary word, and selected central side coordinates. There is no
all-real transition-limit or boundary lift-comparison input. -/
def WalkPhysicalGeometryStatement : Prop :=
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
        ∃ (t : Chart × (ℝ → ℝ) × Finset ℝ) (F : LandingHullFamily t.1),
          IsNormChartPhysical κ b jumps (walkRuns κ b jumps E ω) C t F

/-- The preceding incident-geometry input follows from physical collars.
Every recorded-prefix regularity fact is discharged from staged regularity. -/
theorem walkIncidentGeometryStatement_of_physical
    (hgeom : WalkPhysicalGeometryStatement.{u}) :
    WalkIntGerm.WalkIncidentGeometryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  filter_upwards [hgeom κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts,
    hfacts, hRR, hRL] with ω hω hf hωR hωL C hC
  obtain ⟨t, F, ht⟩ := hω C hC
  have hCoH : IsOpen C ∧ C ⊆ H := by
    rcases hf.2.2.2 C hC with hJ | hU
    · exact ⟨hJ.1, hJ.2.2.1⟩
    · exact ⟨hU.1, hU.2.1⟩
  have hpfR : PrefixBoundaryFacts (walkRuns κ b jumps E ω).1 :=
    prefixBoundaryFacts_run (-(Real.pi / 2)) true _
      (fun j c θ hl => pieceRegular_of_event hωR j c θ hl) (fun j => hreg _ j ω)
  have hpfL : PrefixBoundaryFacts (walkRuns κ b jumps E ω).2 :=
    prefixBoundaryFacts_run (Real.pi / 2) false _
      (fun j c θ hl => pieceRegular_of_event hωL j c θ hl) (fun j => hreg _ j ω)
  obtain ⟨hc, hinc⟩ := isNormChartIncident_of_physical hCoH.1 hCoH.2 hpfR hpfL ht
  exact ⟨t, F.incidentFamily hc, hinc⟩

theorem walkNormChartLocStatement_of_physicalGeometry
    (hgeom : WalkPhysicalGeometryStatement.{u}) : WalkNormChartLocStatement.{u} :=
  WalkIntGerm.walkNormChartLocStatement_of_incidentGeometry
    (walkIncidentGeometryStatement_of_physical hgeom)

theorem walkNormChartStatement_of_physicalGeometry
    (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hS : GW1Z.GW1PieceSimpleStatement.{u})
    (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hG : GW3Sided.GW3GeometryRegStatement.{u})
    (hgeom : WalkPhysicalGeometryStatement.{u}) : WalkNormChartStatement.{u} :=
  WalkIntGerm.walkNormChartStatement_of_incidentGeometry hPR hPL hCO hS hNC hG
    (walkIncidentGeometryStatement_of_physical hgeom)

end InteractingSLE.Theorem14.WalkIntFiber
