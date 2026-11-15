/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Seal.PrepStatements
import InteractingSLE.Spec.Wire.T12Asm6

/-!
# Seal preparation, stage 2 after Lemma R.6: conditional providers of Theorems 1.2 and 1.3 (tops `Wire.T12Asm6`)

PROVE-T12-ASSEMBLE5, round 2 (orchestrator's order). PROVE-SEAL-PREP's stage 2 (`Seal.Prep`, `Spec/Seal/PrepT12`) with
R.6's two-outer faces discharged (PROVE-R6-CORNER): the only open inputs of Theorems 1.2–1.3 are the fibre covers.

* `*_of_covers`: the anchors' providers from the covers `hDy` (universe `u`) and `hDy₀` (universe `0`), through
  `Wire.T12Asm6.theorem12Statement_of_covers` / `theorem13Statement_of_covers`;
* `*_of_restartInputs`: the same from the literal binders of `Wire.T12Asm6.theorem12Statement_assembled6` /
  `theorem13Statement_assembled6` (ruling R102's route with PROVE-AUX61-CAPTURE's component access `CfAccessC`, R103a).

Each provider has exactly its anchor's type after the open inputs (all anchor arguments implicit, `Prop` arguments
auto-parameters), via SEAL-PREP's stage 1 (`Seal.Prep.*_of_statement`).

**R48.** No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or `*_of_param` is an input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Seal.Prep6

open Wire Sec7

/-- **Theorem 1.2's conditional provider** (exactly the anchor's type after the open inputs): the fibre covers at
universes `u` and `0`. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_covers
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
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
  Prep.exists_measurable_lifetime_trace_eq_comp_field_of_statement (T12Asm6.theorem12Statement_of_covers hDy hDy₀)
    hκ hF hcoup

/-- **Theorem 1.3's conditional provider** (exactly the anchor's type after the open input): the universe-`0` fibre
cover. -/
theorem ae_exists_isGeneratingTrace_of_covers
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    {a : ℝ} (ha : 0 < a := by assumption)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  Prep.ae_exists_isGeneratingTrace_of_statement (T12Asm6.theorem13Statement_of_covers hDy₀) ha hF hE

open Sec5 Sec5.Aux61SlitW Sec5.Aux61R1C Sec5.Aux61SlitWX Sec5.Aux61WndCap Sec5.Aux61Cpt in
/-- **Theorem 1.2's conditional provider with the T12Asm6 top's literal binders**: R102's fibre-cover inputs at
universes `u` (`C … hcap`) and `0` (`C₀ … hcap₀`). -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_restartInputs
    (C : ∀ S : SourceSetting.{u}, RestartChoices S)
    (hsel : ∀ S, ∀ i, MeasurableSet ((C S).selected i))
    (V : ∀ S : SourceSetting.{u}, WindowData (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)
    (hSeed : ∀ S : SourceSetting.{u}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C S)).data i).bR 0 =
          sleLambda ((finiteRestart (C S)).data i).κ)
    (haccess : ∀ S : SourceSetting.{u}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart) i p b ∨
          CfAccessC S (Aux61Cmp.normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart) i p b)
    (hcap : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart))) i p)
    (C₀ : ∀ S : SourceSetting.{0}, RestartChoices S)
    (hsel₀ : ∀ S, ∀ i, MeasurableSet ((C₀ S).selected i))
    (V₀ : ∀ S : SourceSetting.{0}, WindowData (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)
    (hSeed₀ : ∀ S : SourceSetting.{0}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C₀ S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C₀ S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C₀ S)).data i).bR 0 =
          sleLambda ((finiteRestart (C₀ S)).data i).κ)
    (haccess₀ : ∀ S : SourceSetting.{0}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)
            i p b ∨
          CfAccessC S (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart) i p b)
    (hcap₀ : ∀ S : SourceSetting.{0}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart))) i p)
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
  Prep.exists_measurable_lifetime_trace_eq_comp_field_of_statement
    (T12Asm6.theorem12Statement_assembled6 C hsel V hSeed haccess hcap C₀ hsel₀ V₀ hSeed₀ haccess₀ hcap₀) hκ hF hcoup

open Sec5 Sec5.Aux61SlitW Sec5.Aux61R1C Sec5.Aux61SlitWX Sec5.Aux61WndCap Sec5.Aux61Cpt in
/-- **Theorem 1.3's conditional provider with the T12Asm6 top's literal binders**: R102's fibre-cover inputs at
universe `0`. -/
theorem ae_exists_isGeneratingTrace_of_restartInputs
    (C₀ : ∀ S : SourceSetting.{0}, RestartChoices S)
    (hsel₀ : ∀ S, ∀ i, MeasurableSet ((C₀ S).selected i))
    (V₀ : ∀ S : SourceSetting.{0}, WindowData (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)
    (hSeed₀ : ∀ S : SourceSetting.{0}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C₀ S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C₀ S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C₀ S)).data i).bR 0 =
          sleLambda ((finiteRestart (C₀ S)).data i).κ)
    (haccess₀ : ∀ S : SourceSetting.{0}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)
            i p b ∨
          CfAccessC S (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart) i p b)
    (hcap₀ : ∀ S : SourceSetting.{0}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart))) i p)
    {a : ℝ} (ha : 0 < a := by assumption)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  Prep.ae_exists_isGeneratingTrace_of_statement
    (T12Asm6.theorem13Statement_assembled6 C₀ hsel₀ V₀ hSeed₀ haccess₀ hcap₀) ha hF hE

end InteractingSLE.Seal.Prep6
