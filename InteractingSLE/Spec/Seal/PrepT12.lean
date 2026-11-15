/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Seal.PrepStatements
import InteractingSLE.Spec.Wire.T12Asm5Final

/-!
# Seal preparation, stage 2: conditional providers of Theorems 1.2 and 1.3 (tops `Wire.T12Asm5`)

Packet PROVE-SEAL-PREP. PROVE-T12-ASSEMBLE5's tops `Wire.T12Asm5.theorem12Statement_assembled5` /
`theorem13Statement_assembled5` leave two open areas:

* **the fibre cover** `Sec5.Aux61Act.DyActFibreCoverOn (¬ IsLargeGap) RefWin`, at universes `u` and `0` (the tops
  build it from ruling R102's binders `C hsel V hSeed haccess hcap` by `T12Asm5.dyCover_of_finiteRestrict_access`);
* **R.6's two-outer faces** in PROVE-R6-TWO's common-time form `hR6Same`.

`theorem12Statement_of_covers` / `theorem13Statement_of_covers` are the tops with the covers themselves as binders
(the tops' proof, with the covers given). They give the conditional providers `*_of_covers` of the two anchors, with
exactly the anchors' types (stage 1, `Seal.Prep.*_of_statement`). `*_of_restartInputs` take the tops' literal binders.

**R48.** No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or `*_of_param` is an input: the only
hypotheses are the covers and `hR6Same` (the T12Asm5 tops are R48-clean, PROVE-T12-ASSEMBLE5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Seal.Prep

open Wire Wire.T12Asm5 Sec7

/-! ### Theorems 1.2 and 1.3 from the two fibre covers and R.6's two-outer faces -/

/-- **Theorem 1.2 from the fibre covers** at universes `u`, `0` and R.6's common-time two-outer faces: the proof of
`T12Asm5.theorem12Statement_assembled5` with the covers given instead of built from R102's binders. -/
theorem theorem12Statement_of_covers
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hR6Same : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tr.R6SameTimeTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0) :
    Exist.Theorem12Statement.{u} := by
  obtain ⟨Ωw, mWord, hB, baseWord, hP, hWordb, hCx⟩ := T12Asm3.exists_physCtx
  obtain ⟨pre, idx, m, X, hXfin, _, hm, hcol⟩ := SideC19.physCtx_exists_reliftedCollar hCx
  exact @theorem12Statement_assembled5_core.{u} hDy hDy₀ R5Init.wordPhase_proved R5Init.outerCont_proved
    (r6Cert_of_leaves5 hDy₀ hR6Same)
    Ωw mWord hB baseWord hP pre idx hWordb hCx.hWordGFF hCx.hWordCF hCx.hWordLife hCx.hWordleft
    hCx.hWordright hCx.hWordθ₁ hCx.hWordθ₂ hCx.hWordu₀ hCx.hWordvα hCx.hWordvL hCx.hWordβc hCx.hWordβ0
    hCx.hWordβm hCx.hWordβtr hCx.hWordηc hCx.hWordηH hCx.hWordη0 hCx.hWordηm hCx.hWordηtr hCx.hWordu
    hCx.hWordub hCx.hWord𝔥 X hXfin m hm
    (fun i => (SideC19.lateSideCollarExcWithChart_shift_iff i _ _ (m i) (X i)).1 (hcol i)) hCx.hRefWord

/-- **Theorem 1.3 from the universe-`0` fibre cover** and R.6's common-time two-outer faces (the proof of
`T12Asm5.theorem13Statement_assembled5` with the cover given). -/
theorem theorem13Statement_of_covers
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hR6Same : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tr.R6SameTimeTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0) :
    Exist.Theorem13Statement.{u} := by
  obtain ⟨Ωw, mWord, hB, baseWord, hP, hWordb, hCx⟩ := T12Asm3.exists_physCtx
  obtain ⟨pre, idx, m, X, hXfin, _, hm, hcol⟩ := SideC19.physCtx_exists_reliftedCollar hCx
  exact @theorem13Statement_assembled5_core.{u} hDy₀ R5Init.wordPhase_proved R5Init.outerCont_proved
    (r6Cert_of_leaves5 hDy₀ hR6Same)
    Ωw mWord hB baseWord hP pre idx hWordb hCx.hWordGFF hCx.hWordCF hCx.hWordLife hCx.hWordleft
    hCx.hWordright hCx.hWordθ₁ hCx.hWordθ₂ hCx.hWordu₀ hCx.hWordvα hCx.hWordvL hCx.hWordβc hCx.hWordβ0
    hCx.hWordβm hCx.hWordβtr hCx.hWordηc hCx.hWordηH hCx.hWordη0 hCx.hWordηm hCx.hWordηtr hCx.hWordu
    hCx.hWordub hCx.hWord𝔥 X hXfin m hm
    (fun i => (SideC19.lateSideCollarExcWithChart_shift_iff i _ _ (m i) (X i)).1 (hcol i))

/-! ### Conditional providers of the Theorem 1.2 and 1.3 anchors -/

/-- **Theorem 1.2's conditional provider** (exactly the anchor's type after the open inputs): the fibre covers at
universes `u`, `0` and R.6's common-time two-outer faces. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_covers
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hR6Same : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tr.R6SameTimeTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
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
  exists_measurable_lifetime_trace_eq_comp_field_of_statement (theorem12Statement_of_covers hDy hDy₀ hR6Same)
    hκ hF hcoup

/-- **Theorem 1.3's conditional provider** (exactly the anchor's type after the open inputs): the universe-`0` fibre
cover and R.6's common-time two-outer faces. -/
theorem ae_exists_isGeneratingTrace_of_covers
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hR6Same : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tr.R6SameTimeTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    {a : ℝ} (ha : 0 < a := by assumption)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  ae_exists_isGeneratingTrace_of_statement (theorem13Statement_of_covers hDy₀ hR6Same) ha hF hE

open Sec5 Sec5.Aux61SlitW Sec5.Aux61R1C Sec5.Aux61SlitWX Sec5.Aux61WndCap in
/-- **Theorem 1.2's conditional provider with the T12Asm5 top's literal binders**: R102's fibre-cover inputs at
universes `u` (`C … hcap`) and `0` (`C₀ … hcap₀`), and `hR6Same`. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_restartInputs
    (C : ∀ S : SourceSetting.{u}, RestartChoices S)
    (hsel : ∀ S, ∀ i, MeasurableSet ((C S).selected i))
    (V : ∀ S : SourceSetting.{u}, WindowData (finiteRestart (C S))
      (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)
    (hSeed : ∀ S : SourceSetting.{u}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C S)).data i).bR 0 =
          sleLambda ((finiteRestart (C S)).data i).κ)
    (haccess : ∀ S : SourceSetting.{u}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C S))
            (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart) i p b ∨
          Aux61Cmp.CfAccess S (Aux61Cmp.normSource (finiteRestart (C S))
            (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart) i p b)
    (hcap : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart))) i p)
    (C₀ : ∀ S : SourceSetting.{0}, RestartChoices S)
    (hsel₀ : ∀ S, ∀ i, MeasurableSet ((C₀ S).selected i))
    (V₀ : ∀ S : SourceSetting.{0}, WindowData (finiteRestart (C₀ S))
      (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)
    (hSeed₀ : ∀ S : SourceSetting.{0}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C₀ S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C₀ S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C₀ S)).data i).bR 0 =
          sleLambda ((finiteRestart (C₀ S)).data i).κ)
    (haccess₀ : ∀ S : SourceSetting.{0}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C₀ S))
            (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart) i p b ∨
          Aux61Cmp.CfAccess S (Aux61Cmp.normSource (finiteRestart (C₀ S))
            (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart) i p b)
    (hcap₀ : ∀ S : SourceSetting.{0}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart))) i p)
    (hR6Same : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tr.R6SameTimeTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
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
  exists_measurable_lifetime_trace_eq_comp_field_of_statement
    (theorem12Statement_assembled5 C hsel V hSeed haccess hcap C₀ hsel₀ V₀ hSeed₀ haccess₀ hcap₀ hR6Same)
    hκ hF hcoup

open Sec5 Sec5.Aux61SlitW Sec5.Aux61R1C Sec5.Aux61SlitWX Sec5.Aux61WndCap in
/-- **Theorem 1.3's conditional provider with the T12Asm5 top's literal binders**: R102's fibre-cover inputs at
universe `0` and `hR6Same`. -/
theorem ae_exists_isGeneratingTrace_of_restartInputs
    (C₀ : ∀ S : SourceSetting.{0}, RestartChoices S)
    (hsel₀ : ∀ S, ∀ i, MeasurableSet ((C₀ S).selected i))
    (V₀ : ∀ S : SourceSetting.{0}, WindowData (finiteRestart (C₀ S))
      (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)
    (hSeed₀ : ∀ S : SourceSetting.{0}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C₀ S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C₀ S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C₀ S)).data i).bR 0 =
          sleLambda ((finiteRestart (C₀ S)).data i).κ)
    (haccess₀ : ∀ S : SourceSetting.{0}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C₀ S))
            (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart) i p b ∨
          Aux61Cmp.CfAccess S (Aux61Cmp.normSource (finiteRestart (C₀ S))
            (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart) i p b)
    (hcap₀ : ∀ S : SourceSetting.{0}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart))) i p)
    (hR6Same : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tr.R6SameTimeTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    {a : ℝ} (ha : 0 < a := by assumption)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  ae_exists_isGeneratingTrace_of_statement
    (theorem13Statement_assembled5 C₀ hsel₀ V₀ hSeed₀ haccess₀ hcap₀ hR6Same) ha hF hE

end InteractingSLE.Seal.Prep
