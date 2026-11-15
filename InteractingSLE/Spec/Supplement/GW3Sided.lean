/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3LawJoint
import InteractingSLE.Spec.Supplement.GW3Orient

/-!
# The between-region geometry of the boundary walks: the R51 form

Packet PROVE-T14-GW7. Theorem GW4, proof (`source/spec/p625-671.md` L235–L241, p. 637): "The ordered-contact Jordan
argument and GB13a consequently apply to these two proper simple curves, with their actual real connectors included.
Their closed between-region is exactly `𝓑 = R ∪ L ∪ ⋃_j C_j`."

The frozen Theorem 1.4 anchors (version 2, ruling R51) assume that every staged family is `StagedPiecesRegular`. This
file states the between-region geometry in that form:

* `GW3GeometrySidedRegStatement` (PROVE-ORIENT's `GW3.GW3GeometrySidedStatement` with the R51 hypothesis) and
  `GW3GeometryRegStatement` (`GW3.GW3GeometryStatement` with it); the unregularized forms imply them;
* `gw3GeometryRegStatement_of_sided`: PROVE-ORIENT's orientation step (`hasOrientedUniformizer_of_isSidedWallPocket`)
  in the R51 form;
* `betweenComponentsOpenRegStatement_of_geometry`, `gw3ChartRegStatement_of_geometry`: the openness of the
  between-components and the existence of component charts (both alternatives of the geometry), in the R51 form;
* `gw3FieldLawRegStatement_of_sided`: Lemma GW3's field law for every choice of charts, R51 form, from the sided
  geometry, the no-common-continuum statement and the one-chart law.

The sided geometry itself is not proved here; the exact missing ingredients are in
`planning/handoffs/PROVE-T14-GW7.md`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW3Sided

/-! ### The statements -/

/-- **Named input: the between-region geometry without orientation, R51 form**: `GW3.GW3GeometrySidedStatement` for
staged families that are also `StagedPiecesRegular`. -/
def GW3GeometrySidedRegStatement : Prop :=
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
      ∀ᵐ ω₀ ∂P,
        ∀ C ∈ betweenComponents
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)),
          GW3.IsTwoArcJordanComponent
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) C ∨
            GW3.IsSidedWallPocket
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) C

/-- **The between-region geometry, R51 form**: `GW3.GW3GeometryStatement` for staged families that are also
`StagedPiecesRegular`. -/
def GW3GeometryRegStatement : Prop :=
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
      ∀ᵐ ω₀ ∂P,
        ∀ C ∈ betweenComponents
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)),
          GW3.IsTwoArcJordanComponent
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) C ∨
            GW3.HasOrientedUniformizer
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) C

/-- **Lemma GW3's charts, R51 form**: `Theorem14.GW3ChartStatement` (every between-component has a component chart)
for staged families that are also `StagedPiecesRegular`. -/
def GW3ChartRegStatement : Prop :=
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
      ∀ᵐ ω₀ ∂P,
        ∀ C ∈ betweenComponents
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)),
          ∃ c : Chart, IsComponentChart
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) C c

/-! ### Bridges from the unregularized forms -/

/-- The unregularized sided geometry implies its R51 form. -/
theorem gw3GeometrySidedRegStatement_of_unreg (hG : GW3.GW3GeometrySidedStatement.{u}) :
    GW3GeometrySidedRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- The unregularized geometry implies its R51 form. -/
theorem gw3GeometryRegStatement_of_unreg (hG : GW3.GW3GeometryStatement.{u}) : GW3GeometryRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-! ### The consequences of the geometry -/

/-- **The orientation part of the geometry, R51 form** (PROVE-ORIENT's `GW3.gw3GeometryStatement_of_sided`): a sided
wall pocket has an oriented uniformizer (`GW3.hasOrientedUniformizer_of_isSidedWallPocket`). -/
theorem gw3GeometryRegStatement_of_sided (hG : GW3GeometrySidedRegStatement.{u}) : GW3GeometryRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω C hC
  rcases hω C hC with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (GW3.hasOrientedUniformizer_of_isSidedWallPocket h2)

/-- **The between-components are open, R51 form**, from the geometry (both alternatives contain openness). -/
theorem betweenComponentsOpenRegStatement_of_geometry (hG : GW3GeometryRegStatement.{u}) :
    GW3Joint.BetweenComponentsOpenRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω C hC
  rcases hω C hC with hJ | hO
  · exact hJ.1
  · exact hO.1

/-- **Lemma GW3's charts, R51 form**, from the geometry (`GW3.exists_isComponentChart_of_geometry`). -/
theorem gw3ChartRegStatement_of_geometry (hG : GW3GeometryRegStatement.{u}) : GW3ChartRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω C hC
  exact GW3.exists_isComponentChart_of_geometry (hω C hC)

/-- **Lemma GW3's field law for every choice of component charts, R51 form**, from the sided geometry, the walks'
no-common-continuum statement and the one-chart law. -/
theorem gw3FieldLawRegStatement_of_sided (hGS : GW3GeometrySidedRegStatement.{u})
    (hN : WalkCont.WalkNoCommonContinuumRegStatement.{u}) (h1 : GW3Joint.GW3FieldLawOneChartRegStatement.{u}) :
    GW3Joint.GW3FieldLawRegStatement.{u} :=
  GW3Joint.gw3FieldLawRegStatement_of_oneChart
    (betweenComponentsOpenRegStatement_of_geometry (gw3GeometryRegStatement_of_sided hGS)) hN h1

end GW3Sided

end Theorem14

end InteractingSLE
