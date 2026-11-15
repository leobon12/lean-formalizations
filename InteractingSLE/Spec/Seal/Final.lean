/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Seal.PrepT1415A6
import InteractingSLE.Spec.Sec5.Aux61CptThm

/-!
# Closed seal providers: Theorems 1.2, 1.3, 1.5 and the staged-history companion

PROVE-T12-ASSEMBLE5, seal round (orchestrator's order after 467745a61). PROVE-AUX61-CAPTURE proved the Prop. 5.1
fibre leaf with no input (`Sec5.Aux61Cpt.cptFibreCover`, every universe; `cptFibreCover₀` at universe `0`), so
Theorems 1.2 and 1.3 are closed (`Aux61Cpt.theorem12Statement_of_cptCover`, `theorem13Statement_of_cptCover`).
Feeding the covers into the conditional providers `Seal.Prep6.*_of_covers` (`Spec/Seal/PrepT12A6`, `PrepT1415A6`)
closes every frozen anchor whose only open inputs were the covers (provider `Seal.Final.<name>`, `<name>` the
anchor's own name unless given):

* Theorem 1.2: `exists_measurable_lifetime_trace_eq_comp_field`;
* Theorem 1.3: `IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`
  (provider `IsIntegratedSLEEvolution_ae_exists_isGeneratingTrace`);
* Theorem 1.4's companion: `exists_isStagedHistory`;
* Theorem 1.5: `IsFlowLine.stays_right_of_lt`, `IsFlowLine.merges`, `IsFlowLine.crosses_of_lt` (seal form, `hx` last)
  (providers `IsFlowLine_stays_right_of_lt`, `IsFlowLine_merges`, `IsFlowLine_crosses_of_lt`) and the companion
  `exists_isFlowLine`.

Each provider has exactly its anchor's type with all arguments implicit and every hypothesis an auto-parameter
`(h : P := by assumption)` (PROVE-COMMON's provider convention; the names are the manifest's provider exports'), so a
sealed anchor body is the bare `by exact <provider>` (through the anchor's `Spec/Provider` module). Theorem 1.4's three
anchors (light cone, frontiers, component kernels) stay open: ROOT2's construction and its four assertions, SB2(1) and
SB4's two launch-tail leaves; their conditional providers with the covers discharged are the `*_of_root`,
`*_of_root_sb` theorems at the end.

Theorem 1.5 as one statement: `theorem15Statement_closed`. No proof content beyond the application.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Seal.Final

open Wire Sec5

/-- **Theorem 1.5, all five clauses, closed** (`Seal.Prep6.theorem15Statement_of_covers` with the proved covers). -/
theorem theorem15Statement_closed : Theorem15Statement.{u} :=
  Prep6.theorem15Statement_of_covers Aux61Cpt.cptFibreCover.{u} Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.2**: closed provider of `InteractingSLE.exists_measurable_lifetime_trace_eq_comp_field`
(exactly its type, all arguments implicit, its hypotheses auto-parameters), from
`Seal.Prep6.exists_measurable_lifetime_trace_eq_comp_field_of_covers` and the proved fibre covers. -/
theorem exists_measurable_lifetime_trace_eq_comp_field
    {κ : ℝ} (hκ : 0 < κ := by assumption) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by assumption) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  by exact Prep6.exists_measurable_lifetime_trace_eq_comp_field_of_covers
      Aux61Cpt.cptFibreCover.{u} Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.3**: closed provider of `InteractingSLE.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`
(exactly its type, all arguments implicit, its hypotheses auto-parameters), from
`Seal.Prep6.ae_exists_isGeneratingTrace_of_covers` and the proved fibre covers. -/
theorem IsIntegratedSLEEvolution_ae_exists_isGeneratingTrace
    {a : ℝ} (ha : 0 < a := by assumption)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  by exact Prep6.ae_exists_isGeneratingTrace_of_covers
      Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.4's companion**: closed provider of `InteractingSLE.exists_isStagedHistory`
(exactly its type, all arguments implicit, its hypotheses auto-parameters), from
`Seal.Prep6.exists_isStagedHistory_of_covers` and the proved fibre covers. -/
theorem exists_isStagedHistory
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) ∧ StagedPiecesRegular κ b jumps P spec (E spec) :=
  by exact Prep6.exists_isStagedHistory_of_covers
      Aux61Cpt.cptFibreCover.{u} Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.5, ordered flow lines**: closed provider of `InteractingSLE.IsFlowLine.stays_right_of_lt`
(exactly its type, all arguments implicit, its hypotheses auto-parameters), from
`Seal.Prep6.stays_right_of_lt_of_covers` and the proved fibre covers. -/
theorem IsFlowLine_stays_right_of_lt
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
  by exact Prep6.stays_right_of_lt_of_covers
      Aux61Cpt.cptFibreCover.{u} Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.5, merging**: closed provider of `InteractingSLE.IsFlowLine.merges`
(exactly its type, all arguments implicit, its hypotheses auto-parameters), from
`Seal.Prep6.merges_of_covers` and the proved fibre covers. -/
theorem IsFlowLine_merges
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
  by exact Prep6.merges_of_covers
      Aux61Cpt.cptFibreCover.{u} Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.5, crossing (seal form, `hx` last)**: closed provider of `InteractingSLE.IsFlowLine.crosses_of_lt`
(exactly its type, all arguments implicit, its hypotheses auto-parameters), from
`Seal.Prep6.crosses_of_lt_of_covers` and the proved fibre covers. -/
theorem IsFlowLine_crosses_of_lt
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
  by exact Prep6.crosses_of_lt_of_covers
      Aux61Cpt.cptFibreCover.{u} Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.5's companion**: closed provider of `InteractingSLE.exists_isFlowLine`
(exactly its type, all arguments implicit, its hypotheses auto-parameters), from
`Seal.Prep6.exists_isFlowLine_of_covers` and the proved fibre covers. -/
theorem exists_isFlowLine
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption) {x θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ :=
  by exact Prep6.exists_isFlowLine_of_covers
      Aux61Cpt.cptFibreCover.{u} Aux61Cpt.cptFibreCover₀

/-! ### Theorem 1.4's three anchors: the covers discharged, ROOT2's and SB's inputs still open -/

/-- **Theorem 1.4, light cone (open: ROOT2's construction and its four assertions)**:
conditional provider of `InteractingSLE.IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`
with the fibre covers discharged (`Seal.Prep6.completedRange_eq_closure_lightCone_of_covers_root`); not closed. -/
theorem IsCenteredCounterflowDriver_completedRange_eq_closure_lightCone_of_root
    (D : Theorem14.GW2TipSystem.RootC24.ConstructionFamily.{u})
    (hCover : Theorem14.GW2TipSystem.RootC24.RootCoverStatement D)
    (hGeometry : Theorem14.GW2TipSystem.RootC24.RootGeometryStatement D)
    (hNear : Theorem14.GW2TipSystem.RootC24.RetainedNearModelsStatement D)
    (hSlow : Theorem14.GW2TipSystem.RootC24.RetainedSlowComparisonsStatement D)
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
  by exact Prep6.completedRange_eq_closure_lightCone_of_covers_root
      Aux61Cpt.cptFibreCover.{u} Aux61Cpt.cptFibreCover₀ D hCover hGeometry hNear hSlow

/-- **Theorem 1.4, frontiers (open: ROOT2's, SB2(1), SB4's two launch tails)**:
conditional provider of `InteractingSLE.IsCenteredCounterflowDriver.boundaryWalks_frontiers`
with the fibre covers discharged (`Seal.Prep6.boundaryWalks_frontiers_of_covers`); not closed. -/
theorem IsCenteredCounterflowDriver_boundaryWalks_frontiers_of_root_sb
    (D : Theorem14.GW2TipSystem.RootC24.ConstructionFamily.{u})
    (hCover : Theorem14.GW2TipSystem.RootC24.RootCoverStatement D)
    (hGeometry : Theorem14.GW2TipSystem.RootC24.RootGeometryStatement D)
    (hNear : Theorem14.GW2TipSystem.RootC24.RetainedNearModelsStatement D)
    (hSlow : Theorem14.GW2TipSystem.RootC24.RetainedSlowComparisonsStatement D)
    (hSB2 : Theorem14.SB.Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (hDS : Theorem14.SB.Ly.SB4DistinctSeedLaunchTailRStatement.{u})
    (hIA : Theorem14.SB.Ly.SB4InitialArcLaunchTailRStatement.{u})
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
  by exact Prep6.boundaryWalks_frontiers_of_covers
      Aux61Cpt.cptFibreCover.{u} Aux61Cpt.cptFibreCover₀ D hCover hGeometry hNear hSlow hSB2 hDS hIA

/-- **Theorem 1.4, component kernels (open: ROOT2's, SB2(1), SB4's two launch tails)**:
conditional provider of `InteractingSLE.IsCenteredCounterflowDriver.componentKernels`
with the fibre covers discharged (`Seal.Prep6.componentKernels_of_covers`); not closed. -/
theorem IsCenteredCounterflowDriver_componentKernels_of_root_sb
    (D : Theorem14.GW2TipSystem.RootC24.ConstructionFamily.{u})
    (hCover : Theorem14.GW2TipSystem.RootC24.RootCoverStatement D)
    (hGeometry : Theorem14.GW2TipSystem.RootC24.RootGeometryStatement D)
    (hNear : Theorem14.GW2TipSystem.RootC24.RetainedNearModelsStatement D)
    (hSlow : Theorem14.GW2TipSystem.RootC24.RetainedSlowComparisonsStatement D)
    (hSB2 : Theorem14.SB.Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (hDS : Theorem14.SB.Ly.SB4DistinctSeedLaunchTailRStatement.{u})
    (hIA : Theorem14.SB.Ly.SB4InitialArcLaunchTailRStatement.{u})
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
  by exact Prep6.componentKernels_of_covers
      Aux61Cpt.cptFibreCover.{u} Aux61Cpt.cptFibreCover₀ D hCover hGeometry hNear hSlow hSB2 hDS hIA

end InteractingSLE.Seal.Final
