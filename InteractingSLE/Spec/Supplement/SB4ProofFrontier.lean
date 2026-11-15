/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm14InputsR51
import InteractingSLE.Spec.Exist.StagedLaw4GW1

/-!
# Theorem 1.4's frontiers under ruling R51, without `GW1PieceProperStatement`

Packet PROVE-T14-SB5 (orchestrator note: rework the SB frontier chain with R51's hypothesis). The version-1 frontier
chain (`SB.sbFrontierStatement_of_inputs` → `SB.sbFrontierStatement_of_sb4` → `SB.boundaryWalks_frontiers_of_sb4`,
`Wire.boundaryWalks_frontiers_of_open5`, `Wire.boundaryWalks_frontiers_of_openR51`) needs GW1's properness
`SB.GW1ProperStatement`, reached through `SB.GW1PieceProperStatement`, which is unprovable for general staged families
(R51). Under the version-2 hypothesis `hreg` (every staged family is `StagedPiecesRegular`), GW1's properness is the
proved `GW1P.gw1ProperRegStatement` (`Spec/Exist/StagedLaw4GW1`). This file reruns the chain with `hreg`:

* `SBFrontierRegStatement` — `SBFrontierStatement` for families that are also `StagedPiecesRegular`;
* `sbFrontierRegStatement_of_inputs` (GW2 + SB), `sbFrontierRegStatement_of_sb4` (GW2, GW0's forward implication and
  SB4's two clauses) — no properness input;
* `boundaryWalks_frontiers_of_inputsReg`, `boundaryWalks_frontiers_of_sb4Reg` — the frontier anchor's version-2 shape;
* **`boundaryWalks_frontiers_of_openReg`** — the version-2 frontier wrapper with the inputs of
  `Wire.boundaryWalks_frontiers_of_openR51` minus `SB.GW1PieceProperStatement`; it uses `hreg`.

Conditional helpers with distinct names; none is a provider.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

/-- **SB's frontier statement for regular families** (`SBFrontierStatement` with R51's hypothesis): almost surely the
completed counterflow range misses the open right side of the lower walk and the open left side of the upper walk. -/
def SBFrontierRegStatement : Prop :=
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
        counterflowCompletedRange (fun t => W' t ω) ∩
            rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅ ∧
          counterflowCompletedRange (fun t => W' t ω) ∩
            leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅

/-- **The frontier input for regular families from GW2 and SB** (the argument of `sbFrontierStatement_of_inputs`,
with GW1's properness from `GW1P.gw1ProperRegStatement`). -/
theorem sbFrontierRegStatement_of_inputs (hGW2 : GW2LightConeStatement.{u}) (hSB : SBStatement.{u}) :
    SBFrontierRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hΘ : Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ) ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    inter_subset_left
  have hΘc : (Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ)).Countable :=
    (countable_range _).mono inter_subset_right
  have hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆
      closure (Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ)) :=
    Dense.open_subset_closure_inter Rat.denseRange_cast isOpen_Ioo
  obtain ⟨Q, hQc, -, -, hQ⟩ := hGW2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hΘ hΘc hΘd
  filter_upwards [hQ E hE, hSB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _ hΘ hΘc Q hQc,
    GW1P.gw1ProperRegStatement κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω hω hsb hpr
  rw [← hω]
  refine ⟨closure_inter_eq_empty (isOpen_rightSideOf hpr.1) ?_, closure_inter_eq_empty (isOpen_leftSideOf hpr.2) ?_⟩
  · rw [union_inter_distrib_right, hsb.1, empty_union]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hz0, hzR⟩ := hz
    rw [mem_singleton_iff] at hz0
    subst hz0
    exact ofReal_notMem_H 0 (by simpa using hzR.1.1)
  · rw [union_inter_distrib_right, hsb.2, empty_union]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hz0, hzL⟩ := hz
    rw [mem_singleton_iff] at hz0
    subst hz0
    exact ofReal_notMem_H 0 (by simpa using hzL.1.1)

/-- **The frontier input for regular families from SB4's two clauses** (GW2, GW0's forward implication, SB4's
distinct-seed and initial-arc clauses; no properness input). -/
theorem sbFrontierRegStatement_of_sb4 (hGW2 : GW2LightConeStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hDS : SB4DistinctSeedStatement.{u}) (hIA : SB4InitialArcStatement.{u}) : SBFrontierRegStatement.{u} :=
  sbFrontierRegStatement_of_inputs hGW2
    (sbStatement_of_sb4_sb5 (sb4Statement_of_distinctSeed hDS) (sb5Statement_of_inputs hGW0 hIA hDS))

/-- **Theorem 1.4, frontiers, version 2, from its three inputs** (`Theorem14.boundaryWalks_frontiers_of_inputs` with
`SBFrontierRegStatement` and R51's hypothesis). -/
theorem boundaryWalks_frontiers_of_inputsReg (hGW2a : GW2aContainmentStatement.{u})
    (hSB : SBFrontierRegStatement.{u}) (hGW6 : GW6Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec)) :
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
          (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤) := by
  have hpi := Real.pi_pos
  have hR := hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
      ⟨le_rfl, by linarith⟩ true)
  have hL := hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2)
      ⟨by linarith, le_rfl⟩ false)
  filter_upwards [hR, hL, hSB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hGW6 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω h1 h2 h3 h4
  exact ⟨⟨h1, h3.1⟩, ⟨h2, h3.2⟩, h4⟩

/-- **Theorem 1.4, frontiers, version 2** (R51), provider shape, from Lemma GW2a, Lemma GW2, Lemma GW0's forward
implication and SB4's two clauses; GW1's properness comes from `hreg` (conditional helper; not the provider). -/
theorem boundaryWalks_frontiers_of_sb4Reg (hGW2a : GW2aContainmentStatement.{u})
    (hGW2 : GW2LightConeStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u}) (hDS : SB4DistinctSeedStatement.{u})
    (hIA : SB4InitialArcStatement.{u})
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
  boundaryWalks_frontiers_of_inputsReg hGW2a (sbFrontierRegStatement_of_sb4 hGW2 hGW0 hDS hIA)
    (gw6Statement_of_gw2a hGW2a GW1.gw1FirstThresholdStatement) hκ hκ4 b jumps hb hh hcf hζ' E hE hreg

/-- **Theorem 1.4, frontiers, version 2** (`IsCenteredCounterflowDriver.boundaryWalks_frontiers`, R51), provider
shape, from the inputs of `Wire.boundaryWalks_frontiers_of_openR51` without `SB.GW1PieceProperStatement`: Lemma GW2's
inputs (Theorem 1.3, BR6, the two schedule containments, the exhaustion), Theorem 1.3 at universe `0` (GW0's forward
implication), Lemma GW2a and SB4's distinct-seed and initial-arc clauses (conditional helper; not the provider). -/
theorem boundaryWalks_frontiers_of_openReg (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u})
    (hC0 : GW2Cone.GW2ScheduleContainmentStatement.{u}) (hCv : GW2Cone.GW2ArcScheduleContainmentStatement.{u})
    (hEx : GW2Cone.GW2TipExhaustionStatement.{u}) (hGW2a : GW2aContainmentStatement.{u})
    (hDS : SB4DistinctSeedStatement.{u}) (hIA : SB4InitialArcStatement.{u})
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
  boundaryWalks_frontiers_of_sb4Reg hGW2a (Wire.gw2LightConeStatement_of_open5 h13 h13₀ hBR6 hC0 hCv hEx)
    (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hDS hIA hκ hκ4 hb hh hcf hζ' hE hreg

end SB

end Theorem14

end InteractingSLE
