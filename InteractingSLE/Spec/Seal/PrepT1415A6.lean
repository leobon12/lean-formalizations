/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Seal.PrepT1415
import InteractingSLE.Spec.Seal.PrepT12A6

/-!
# Seal preparation, stage 3 after Lemma R.6: providers of the Theorem 1.4 and 1.5 anchors without `hR6Same`

PROVE-T12-ASSEMBLE5, round 2 (orchestrator's order). PROVE-SEAL-PREP's stage 3 (`Seal.Prep`, `Spec/Seal/PrepT1415`)
with R.6's two-outer faces discharged (PROVE-R6-CORNER, `R6Cor.twoFaces_proved`): Theorems 1.2–1.3 enter through
`Wire.T12Asm6.theorem12Statement_of_covers` / `theorem13Statement_of_covers`, whose only inputs are the fibre covers
`hDy`/`hDy₀`. The providers below are SEAL-PREP's (same names, namespace `Seal.Prep6`, bodies verbatim) with the binder
`hR6Same` deleted; every one still has exactly its anchor's type after its open inputs (`crosses_of_lt` in seal form,
`hx` last). Open inputs per anchor (section variables):

| anchor | open inputs |
|---|---|
| `exists_isStagedHistory` | `hDy hDy₀` |
| `completedRange_eq_closure_lightCone` | `hDy hDy₀` + ROOT2's `D hCover hGeometry hNear hSlow` |
| `boundaryWalks_frontiers`, `componentKernels` | the above + `hSB2 hDS hIA` (`Wire.theorem14Statement_assembled5`) |
| Theorem 1.5's three clauses and `exists_isFlowLine` | `hDy hDy₀` (`Wire.theorem15Statement_assembled2`) |

The T14/T15 Wire tops themselves (`T14Asm5`, `T1415Asm2`) take Theorems 1.2–1.3 as inputs and never had `hR6Same`.
R48 does not restrict these: Theorems 1.2–1.3 are permitted inputs of Theorems 1.4–1.5.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Seal.Prep6

open Wire Theorem14

/-! ### Providers needing only Theorems 1.2–1.3 (the fibre covers) -/

section Covers

variable (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
  Sec5.Aux61Cov.RefWin)
variable (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
  Sec5.Aux61Cov.RefWin)

include hDy hDy₀

/-- **Theorem 1.5, all five clauses**, from the fibre covers (`Wire.theorem15Statement_assembled2` with
Theorems 1.2–1.3 from `Wire.T12Asm6`). -/
theorem theorem15Statement_of_covers : Theorem15Statement.{u} :=
  theorem15Statement_assembled2
    (T12Asm6.theorem12Statement_of_covers.{u} hDy hDy₀)
    (T12Asm6.theorem13Statement_of_covers.{u} hDy₀)
    (T12Asm6.theorem12Statement_of_covers.{0} hDy₀ hDy₀)
    (T12Asm6.theorem13Statement_of_covers.{0} hDy₀)
    hDy hDy₀

/-- **Theorem 1.4's companion `exists_isStagedHistory`, conditional provider**: Theorems 1.2–1.3 only. -/
theorem exists_isStagedHistory_of_covers
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) ∧ StagedPiecesRegular κ b jumps P spec (E spec) :=
  by exact Prep.exists_isStagedHistory_of_statement (fun {κ} hκ hκ4 {b jumps} hb {Ω} _ _ {P} _ {h} hh =>
      exists_isStagedHistory_of_wire6 (T12Asm6.theorem12Statement_of_covers.{u} hDy hDy₀)
        (T12Asm6.theorem13Statement_of_covers.{u} hDy₀) hκ hκ4 hb hh)

/-- **Theorem 1.5's `IsFlowLine.stays_right_of_lt`, conditional provider.** -/
theorem stays_right_of_lt_of_covers
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁ := by assumption) (hθ : θ₁ < θ₂ := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ := by assumption)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ := by assumption) :
    (∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        ¬ IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) :=
  by exact Prep.stays_right_of_lt_of_statement (theorem15Statement_of_covers hDy hDy₀).1

/-- **Theorem 1.5's `IsFlowLine.merges`, conditional provider.** -/
theorem merges_of_covers
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x₁ x₂ θ : ℝ} (hx : x₂ ≤ x₁ := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ P h η₁ ζ₁ := by assumption)
    (hη₂ : IsFlowLine κ b jumps x₂ θ P h η₂ ζ₂ := by assumption) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
      AgreeAsCurvesAfter (η₁ ω) (ζ₁ ω) s (η₂ ω) (ζ₂ ω) t :=
  by exact Prep.merges_of_statement (theorem15Statement_of_covers hDy hDy₀).2.1

/-- **Theorem 1.5's `IsFlowLine.crosses_of_lt`, conditional provider** (seal form: `hx` last). -/
theorem crosses_of_lt_of_covers
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hθ : θ₂ < θ₁ := by assumption)
    (hθπ : θ₁ < θ₂ + Real.pi := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ := by assumption)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ := by assumption)
    (hx : x₂ < x₁ := by assumption) :
    (∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
        ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
          CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
          IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) :=
  by exact Prep.crosses_of_lt_of_statement (theorem15Statement_of_covers hDy hDy₀).2.2.1

/-- **Theorem 1.5's companion `exists_isFlowLine`, conditional provider.** -/
theorem exists_isFlowLine_of_covers
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption) {x θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ :=
  by exact Prep.exists_isFlowLine_of_statement (theorem15Statement_of_covers hDy hDy₀).2.2.2.1

/-! ### Providers also needing GW2's root construction (ROOT2's four assertions) -/

section Root

variable (D : GW2TipSystem.RootC24.ConstructionFamily.{u})
variable (hCover : GW2TipSystem.RootC24.RootCoverStatement D)
variable (hGeometry : GW2TipSystem.RootC24.RootGeometryStatement D)
variable (hNear : GW2TipSystem.RootC24.RetainedNearModelsStatement D)
variable (hSlow : GW2TipSystem.RootC24.RetainedSlowComparisonsStatement D)

include D hCover hGeometry hNear hSlow

/-- **Theorem 1.4's light-cone clause** from the fibre covers and ROOT2's construction with its four open
assertions (`GW2TipSystem.RootC24.gw2RootTestStatement_of_oneSided_comparisons`). -/
theorem lightCone14Statement_of_covers_root : LightCone14Statement.{u} :=
  Prep.lightCone14Statement_of_thm12_thm13_tests
    (T12Asm6.theorem12Statement_of_covers.{u} hDy hDy₀)
    (T12Asm6.theorem13Statement_of_covers.{u} hDy₀)
    (T12Asm6.theorem12Statement_of_covers.{0} hDy₀ hDy₀)
    (T12Asm6.theorem13Statement_of_covers.{0} hDy₀)
    (GW2TipSystem.RootC24.gw2RootTestStatement_of_oneSided_comparisons
      (T12Asm6.theorem13Statement_of_covers.{u} hDy₀) D hCover hGeometry hNear hSlow)

/-- **Theorem 1.4's light cone `IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`, conditional
provider.** -/
theorem completedRange_eq_closure_lightCone_of_covers_root
    {κ : ℝ} (hκ : 0 < κ := by assumption)
    (hκ4 : κ < 4 := by assumption) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
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
  by exact Prep.completedRange_eq_closure_lightCone_of_statement
      (lightCone14Statement_of_covers_root hDy hDy₀ D hCover hGeometry hNear hSlow)

/-! ### Providers needing the whole Theorem 1.4 top (also SB2(1) and SB4's two launch-tail leaves) -/

section SB

variable (hSB2 : SB.Ly.SB2UpperLaunchEntryLAmbStatement.{u})
variable (hDS : SB.Ly.SB4DistinctSeedLaunchTailRStatement.{u})
variable (hIA : SB.Ly.SB4InitialArcLaunchTailRStatement.{u})

include hSB2 hDS hIA

/-- **Theorem 1.4, all four clauses**, from the fibre covers, ROOT2's construction with its four open
assertions, SB2(1) and SB4's two launch-tail leaves (`Wire.theorem14Statement_assembled5`). -/
theorem theorem14Statement_of_covers : Theorem14Statement.{u} :=
  theorem14Statement_assembled5
    (T12Asm6.theorem12Statement_of_covers.{u} hDy hDy₀)
    (T12Asm6.theorem13Statement_of_covers.{u} hDy₀)
    (T12Asm6.theorem12Statement_of_covers.{0} hDy₀ hDy₀)
    (T12Asm6.theorem13Statement_of_covers.{0} hDy₀)
    D hCover hGeometry hNear hSlow hSB2 hDy hDy₀ hDS hIA

/-- **Theorem 1.4's `IsCenteredCounterflowDriver.boundaryWalks_frontiers`, conditional provider.** -/
theorem boundaryWalks_frontiers_of_covers
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
  by exact Prep.boundaryWalks_frontiers_of_statement
      (theorem14Statement_of_covers hDy hDy₀ D hCover hGeometry hNear hSlow hSB2 hDS hIA).2.1

/-- **Theorem 1.4's `IsCenteredCounterflowDriver.componentKernels`, conditional provider.** -/
theorem componentKernels_of_covers
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
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  by exact Prep.componentKernels_of_statement
      (theorem14Statement_of_covers hDy hDy₀ D hCover hGeometry hNear hSlow hSB2 hDS hIA).2.2.1

end SB

end Root

end Covers

end InteractingSLE.Seal.Prep6
