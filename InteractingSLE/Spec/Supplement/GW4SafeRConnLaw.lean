/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRConnRun
import InteractingSLE.Spec.Supplement.WalkUnionLawMain

/-!
# GW4: the connector height bounds for the actual R51 histories

Regularize the staged family using the existing adapter, apply Theorem 1.3's
stage-exit classification, and return to the original connector lists by the
almost-sure equality of runs. No connector-height assumption is added.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish GW1WalkExit

/-- Both actual extreme walks satisfy the recorded-connector height bound,
under the original R51 staged-history assumptions. -/
theorem ae_walkConnectorHeightBounds (h13₀ : Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b J P h spec (E spec))
    (hPieces : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b J P spec (E spec)) (right : Bool) :
    ∀ᵐ ω ∂P, WalkConnectorHeightBounds κ b J (GW1Z.walkSpec b J right)
      (fun j => E (GW1Z.walkSpec b J right) j ω) right := by
  obtain ⟨hE₁, hreg₁, hrun⟩ := StagedReg.regFam_spec hb hE hPieces
  let spec := GW1Z.walkSpec b J right
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b J
    (GW1Z.walkAngle_mem_Icc right) right
  have hS := walkStageData_of_theorem13 h13₀ κ hκ hκ4 b J hb P h hh W' ζ' hcf hζ'
    (StagedReg.regFam E) hE₁ hreg₁ right
  have hP := (WalkLaw.stagedPiecesRegular_regHist (hPieces spec hprog)).ae_pieceRegular
  filter_upwards [hS, hP, hrun spec hprog] with ω hs hp hr
  have hH := walkConnectorHeightBounds_of_stageData hκ hb
    (fun j => StagedReg.regFam E spec j ω) (fun j => hreg₁ spec j ω) hs hp
  unfold WalkConnectorHeightBounds at hH ⊢
  rwa [hr spec.2.2.length] at hH

end InteractingSLE.Theorem14.GW4Fix
