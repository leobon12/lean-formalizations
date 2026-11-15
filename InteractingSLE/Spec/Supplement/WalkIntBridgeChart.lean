/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBridgeMatch

/-!
# GW3 normalization conditional on the retained-prefix geometry

The named hypothesis records the remaining new geometry explicitly, as
authorized by the continuation order. It supplies boundary correspondences
and retained-prefix references, but supplies no boundary integer. All integer
coherence and normalization are proved from those geometric data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkIntBridge

open WalkMean WalkBdry WalkNorm

/-- The remaining GW3 geometric input: finite boundary correspondence with a
family of retained-prefix charts and zero inherited-lift comparisons. Exact
data are `ReferenceFamily` and `IsNormChartRef`. No integer is an input. -/
def WalkReferenceGeometryStatement : Prop :=
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
        ∃ (t : Chart × (ℝ → ℝ) × Finset ℝ) (F : ReferenceFamily t.1),
          IsNormChartRef κ b jumps (walkRuns κ b jumps E ω) C t F

/-- Discharge the existing local chart leaf from the named geometric input.
One integer is chosen before quantifying over any of the component matches. -/
theorem walkNormChartLocStatement_of_referenceGeometry
    (hgeom : WalkReferenceGeometryStatement.{u}) : WalkNormChartLocStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  filter_upwards [hgeom κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts,
    hfacts] with ω hω hf C hC
  obtain ⟨t, F, ht⟩ := hω C hC
  have hCoH : IsOpen C ∧ C ⊆ H := by
    rcases hf.2.2.2 C hC with hJ | hU
    · exact ⟨hJ.1, hJ.2.2.1⟩
    · exact ⟨hU.1, hU.2.1⟩
  obtain ⟨n, hn⟩ := exists_isNormChartLoc_of_ref hCoH.1 hCoH.2 ht
  exact ⟨t, n, hn⟩

/-- The existing normalized-chart leaf follows after the reference geometry;
the original almost sure path facts are supplied by the existing wiring. -/
theorem walkNormChartStatement_of_referenceGeometry
    (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hS : GW1Z.GW1PieceSimpleStatement.{u})
    (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hG : GW3Sided.GW3GeometryRegStatement.{u})
    (hgeom : WalkReferenceGeometryStatement.{u}) : WalkNormChartStatement.{u} :=
  walkNormChartStatement_of_loc hPR hPL hCO hS hNC hG
    (walkNormChartLocStatement_of_referenceGeometry hgeom)

end InteractingSLE.Theorem14.WalkIntBridge
