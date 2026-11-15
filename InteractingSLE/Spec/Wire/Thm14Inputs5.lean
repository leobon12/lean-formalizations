/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm14Inputs2
import InteractingSLE.Spec.Supplement.GW2ConeArc
import InteractingSLE.Spec.Supplement.BR3Ref
import InteractingSLE.Spec.Supplement.SB4
import InteractingSLE.Spec.Supplement.GW3Chart
import InteractingSLE.Spec.Supplement.GW4KernelLife
import InteractingSLE.Spec.Exist.StagedLaw2Main
import InteractingSLE.Spec.Exist.StagedLaw2Stop
import InteractingSLE.Spec.Exist.Param12Canonical
import InteractingSLE.Spec.Exist.StagedLaw3Main
import InteractingSLE.Spec.Supplement.GW3LawEvery
import InteractingSLE.Spec.Supplement.GW3Orient

/-!
# Theorem 1.4 with the results landed since PROVE-WIRE3 plugged in

Packet PROVE-WIRE5 (no new mathematics). Theorems 1.2 and 1.3 enter only as the types of their frozen anchors
(`Exist.Theorem12Statement`, `Exist.Theorem13Statement`). Since PROVE-WIRE3:

* **light cone.** Lemma GW2 follows from Theorem 1.3, BR6, GW0's forward implication, the two schedule containments and
  the exhaustion at interior tips (`GW2Cone.gw2LightConeStatement_of_br6`, PROVE-T14-CONE); GW0's forward implication
  follows from Theorem 1.3 at universe `0` (`BR3Ref.gw0ForwardStatement_of_theorem13`, PROVE-T14-BR3). Lemma GW2a stays
  one input (PROVE-T14-BR4 runs on it);
* **frontiers.** `SBFrontierStatement` follows from GW2, GW0's forward implication, SB4's distinct-seed and initial-arc
  clauses and GW1's properness (`SB.sbFrontierStatement_of_sb4`, PROVE-T14-SB2, with SB5 proved), and the properness
  from its per-piece form (`SB.gw1ProperStatement_of_pieces`);
* **component kernels.** GW3's chart statement follows from the between-region geometry
  (`GW3.gw3ChartStatement_of_geometry`), the geometry from its conformal-map-free sided form
  (`GW3.gw3GeometryStatement_of_sided`, PROVE-ORIENT); GW4's kernel statement from GW3's field law, GW4's traversal
  core, GW3's word bounds and Theorems 1.2–1.3 (`GW4.gw4KernelStatement_of_thm12`, `GW4.gw4TraversalStatement_of_core`,
  PROVE-T14-GW4); the field law from the one-chart law and the no-common-continuum statement, the word bounds from GW0's
  forward implication and the connector side (`GW3Law.gw3FieldLawStatement_of_oneChart`,
  `GW3Word.gw3WordBoundStatement_of_inputs`, `GW3Word.betweenComponentsOpenStatement_of_geometry`, PROVE-T14-GW5);
* **companion.** The staged-history construction follows from the word-measurable Theorem 1.2, Theorem 1.3 and the
  single-stage law (`StagedLaw.stagedHistoryConstructionStatement_of_stopLaw'`, PROVE-STAGEDLAW2), which is proved
  (`StagedLaw.stopCondLawStatement`, PROVE-STAGEDLAW3); the word-measurable Theorem 1.2 follows from Theorems 1.2–1.3
  (`Param12.theorem12ParamStatement_of_thm12_thm13`, PROVE-PARAM12C). So the companion needs Theorems 1.2–1.3 alone.

Every theorem here is a conditional helper with a distinct name; none is a provider.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

open Theorem14

/-! ### Lemma GW2 -/

/-- **Lemma GW2** (`Theorem14.GW2LightConeStatement`) from Theorem 1.3 (frozen type, at `u` and at `0`), BR6, the two
schedule containments and the exhaustion at interior tips: GW0's forward implication is Theorem 1.3's consequence
`BR3Ref.gw0ForwardStatement_of_theorem13`. -/
theorem gw2LightConeStatement_of_open5 (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u})
    (hC0 : GW2Cone.GW2ScheduleContainmentStatement.{u}) (hCv : GW2Cone.GW2ArcScheduleContainmentStatement.{u})
    (hEx : GW2Cone.GW2TipExhaustionStatement.{u}) : GW2LightConeStatement.{u} :=
  GW2Cone.gw2LightConeStatement_of_br6 h13 hBR6 (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hC0 hCv hEx

/-! ### The light cone -/

/-- **Theorem 1.4, light cone** (`IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`), provider shape,
from Theorem 1.3 (frozen type, at `u` and `0`), BR6, the two schedule containments of GW2, GW2's exhaustion at interior
tips and Lemma GW2a (conditional helper; not the provider). -/
theorem completedRange_eq_closure_lightCone_of_open5 (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u})
    (hC0 : GW2Cone.GW2ScheduleContainmentStatement.{u}) (hCv : GW2Cone.GW2ArcScheduleContainmentStatement.{u})
    (hEx : GW2Cone.GW2TipExhaustionStatement.{u}) (hGW2a : GW2aContainmentStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {Θ : Set ℝ} (hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by assumption)
    (hΘc : Θ.Countable := by assumption)
    (hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ := by assumption) :
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
            counterflowCompletedRange (fun t => W' t ω)) ∧
        ∀ 𝒞 : Set (List Instr), 𝒞.Countable → (∀ p ∈ 𝒞, IsBoundaryContinuedProgram p) →
          ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪
              (⋃ p ∈ 𝒞, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω)) ∪
              {0}) =
            counterflowCompletedRange (fun t => W' t ω) :=
  completedRange_eq_closure_lightCone_of_remaining2 (gw2LightConeStatement_of_open5 h13 h13₀ hBR6 hC0 hCv hEx)
    hGW2a hκ hκ4 hb hh hcf hζ' hΘ hΘc hΘd

/-! ### The frontiers -/

/-- **SB's frontier statement** (`Theorem14.SBFrontierStatement`) from Lemma GW2's inputs, Theorem 1.3 at universe `0`
(GW0's forward implication), SB4's distinct-seed and initial-arc clauses and GW1's per-piece properness. -/
theorem sbFrontierStatement_of_open5 (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u})
    (hC0 : GW2Cone.GW2ScheduleContainmentStatement.{u}) (hCv : GW2Cone.GW2ArcScheduleContainmentStatement.{u})
    (hEx : GW2Cone.GW2TipExhaustionStatement.{u}) (hDS : SB.SB4DistinctSeedStatement.{u})
    (hIA : SB.SB4InitialArcStatement.{u}) (hPP : SB.GW1PieceProperStatement.{u}) : SBFrontierStatement.{u} :=
  SB.sbFrontierStatement_of_sb4 (gw2LightConeStatement_of_open5 h13 h13₀ hBR6 hC0 hCv hEx)
    (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hDS hIA (SB.gw1ProperStatement_of_pieces hPP)

/-- **Theorem 1.4, frontiers** (`IsCenteredCounterflowDriver.boundaryWalks_frontiers`), provider shape, from Lemma
GW2a, Lemma GW2's inputs (Theorem 1.3, BR6, the two schedule containments, the exhaustion), SB4's distinct-seed and
initial-arc clauses and GW1's per-piece properness (conditional helper; not the provider). -/
theorem boundaryWalks_frontiers_of_open5 (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u})
    (hC0 : GW2Cone.GW2ScheduleContainmentStatement.{u}) (hCv : GW2Cone.GW2ArcScheduleContainmentStatement.{u})
    (hEx : GW2Cone.GW2TipExhaustionStatement.{u}) (hGW2a : GW2aContainmentStatement.{u})
    (hDS : SB.SB4DistinctSeedStatement.{u}) (hIA : SB.SB4InitialArcStatement.{u})
    (hPP : SB.GW1PieceProperStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption) :
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
  SB.boundaryWalks_frontiers_of_sb4 hGW2a (gw2LightConeStatement_of_open5 h13 h13₀ hBR6 hC0 hCv hEx)
    (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hDS hIA (SB.gw1ProperStatement_of_pieces hPP) hκ hκ4 hb hh hcf hζ' hE

/-! ### The component kernels -/

/-- **Theorem GW4's kernel statement** (`Theorem14.GW4KernelStatement`) from GW3's field law, GW3's word bounds, GW4's
traversal core and Theorems 1.2–1.3 (frozen types). -/
theorem gw4KernelStatement_of_open5 (hF : GW4.GW3FieldLawStatement.{u}) (hWB : GW4.GW3WordBoundStatement.{u})
    (hT : GW4.GW4TraversalCoreStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : GW4KernelStatement.{u} :=
  GW4.gw4KernelStatement_of_thm12 hF (GW4.gw4TraversalStatement_of_core hT hWB) h12 h13

/-- **Theorem GW4's kernel statement** from the finest landed inputs: GW3's sided geometry, the one-chart field law,
the no-common-continuum statement, the connector side, GW4's traversal core and Theorems 1.2–1.3 (frozen types; at
universe `0` for GW0's forward implication). -/
theorem gw4KernelStatement_of_sided5 (hGS : GW3.GW3GeometrySidedStatement.{u})
    (hF1 : GW3Law.GW3FieldLawOneChartStatement.{u}) (hN : GW3Law.WalkNoCommonContinuumStatement.{u})
    (hS : GW3Word.WalkConnectorSideStatement.{u}) (hT : GW4.GW4TraversalCoreStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) : GW4KernelStatement.{u} :=
  gw4KernelStatement_of_open5
    (GW3Law.gw3FieldLawStatement_of_oneChart
      (GW3Word.betweenComponentsOpenStatement_of_geometry (GW3.gw3GeometryStatement_of_sided hGS)) hN hF1)
    (GW3Word.gw3WordBoundStatement_of_inputs
      (GW3Word.betweenComponentsOpenStatement_of_geometry (GW3.gw3GeometryStatement_of_sided hGS))
      (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hS) hT h12 h13

/-- **Theorem 1.4, component kernels** (`IsCenteredCounterflowDriver.componentKernels`), provider shape, from GW3's
sided geometry, the one-chart field law, the no-common-continuum statement, the connector side, GW4's traversal core
and Theorems 1.2–1.3 (frozen types, at `u` and `0`) (conditional helper; not the provider). -/
theorem componentKernels_of_open5 (hGS : GW3.GW3GeometrySidedStatement.{u})
    (hF1 : GW3Law.GW3FieldLawOneChartStatement.{u}) (hN : GW3Law.WalkNoCommonContinuumStatement.{u})
    (hS : GW3Word.WalkConnectorSideStatement.{u}) (hT : GW4.GW4TraversalCoreStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption) :
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
  componentKernels_of_remaining2 (GW3.gw3ChartStatement_of_geometry (GW3.gw3GeometryStatement_of_sided hGS))
    (gw4KernelStatement_of_sided5 hGS hF1 hN hS hT h12 h13 h13₀) hκ hκ4 hb hh hcf hζ' hE

/-! ### The companion `exists_isStagedHistory` -/

/-- **The staged-history construction** (`Theorem14.StagedHistoryConstructionStatement`) from Theorems 1.2–1.3 (frozen
types) alone: the conditional law at the stop is proved (`StagedLaw.stopCondLawStatement`, PROVE-STAGEDLAW3). -/
theorem stagedHistoryConstructionStatement_of_open5 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : StagedHistoryConstructionStatement.{u} :=
  Exist.StagedLaw.stagedHistoryConstructionStatement_of_stopLaw'
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
    (Exist.StagedLaw.stopLawStatement_of_stopCondLaw Exist.StagedLaw.stopCondLawStatement)

/-- **The companion of Theorem 1.4** (`exists_isStagedHistory`), provider shape, from Theorems 1.2–1.3 (frozen types)
alone (conditional helper; not the provider). -/
theorem exists_isStagedHistory_of_open5 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec,
      IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec) :=
  exists_isStagedHistory_of_remaining2 (stagedHistoryConstructionStatement_of_open5 h12 h13) hκ hκ4 hb hh

end Wire

end InteractingSLE
