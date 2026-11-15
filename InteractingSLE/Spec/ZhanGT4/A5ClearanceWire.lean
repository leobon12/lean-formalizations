/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceMain
import InteractingSLE.Spec.ZhanGT4.ClearanceWire
import InteractingSLE.Spec.ZhanGT4.ClearanceWordsRef

/-!
# Protected-ray clearance, VIII: the consumers of (G2) with the clearance input discharged

Packet PROVE-ZHAN-CLEAR. `A5Clear.separatedClearanceStatement` proves `SeparatedClearanceStatement κ` for every
`κ > 4`, so every clearance twin of PROVE-ZHAN-R53W (`ClearanceNoCluster`, `ClearanceWordsRef`, `ClearanceWords`,
`ClearanceWire`) now needs only Part A's (G5) (`StoppingInverseBoundaryStatement`, the inverse boundary at positive
stopping times of ordinary `SLE_κ`). This file states those consequences (`*_of_inverseBoundary`), and the Part A input
of Section 5 at `16/κ` from (G5) alone (`Sec5.partAInputsSixteenDivOfClearance_of_inverseBoundary`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-- **Lemma 3.4 of the additional note for `κ > 4`, from (G5) alone**: separated two-force laws with weights `≥ κ/2 − 2`
have no real terminal cluster point. -/
theorem separatedNoRealClusterStatement_of_inverseBoundary {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{u} κ) : SeparatedNoRealClusterStatement.{u} κ :=
  separatedNoRealClusterStatement_of_clearance hκ4 hG5 (A5Clear.separatedClearanceStatement κ)

/-- Lemma 3.4 from the stopping-time collar (G7) alone. -/
theorem separatedNoRealClusterStatement_of_collar' {κ : ℝ} (hκ4 : 4 < κ) (hG7 : StoppingCollarStatement.{u} κ) :
    SeparatedNoRealClusterStatement.{u} κ :=
  separatedNoRealClusterStatement_of_collar_of_clearance hκ4 hG7 (A5Clear.separatedClearanceStatement κ)

/-- **Two-seed transience for `κ > 4`** from (G5) alone. -/
theorem twoSeedTransienceStatement_of_gt_four_of_inverseBoundary {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) : TwoSeedTransienceStatement.{u} κ :=
  twoSeedTransienceStatement_of_gt_four_of_clearance hκ4 hG5 (A5Clear.separatedClearanceStatement κ)

/-- **Separated two-force transience for `κ > 4`** from (G5) alone. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_gt_four_of_inverseBoundary {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop :=
  IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_gt_four_of_clearance hκ4 hG5
    (A5Clear.separatedClearanceStatement κ) hxL hxR hadm hE

/-- **Transience for two-group words, `κ > 4`**, from (G5) alone. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_groups_gt_four_of_inverseBoundary {κ : ℝ} {nL nR : ℕ}
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ4 : 4 < κ) (hG5 : StoppingInverseBoundaryStatement.{0} κ)
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) (hgL : ∀ i j, xL i = xL j) (hgR : ∀ i j, xR i = xR j)
    (hn : 0 < nL + nR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop :=
  IsIntegratedSLEEvolution.ae_tendsto_norm_trace_groups_gt_four_of_clearance hκ4 hG5
    (A5Clear.separatedClearanceStatement κ) hF hadm hxL hxR hgL hgR hn hE

/-- **Transience for every separated word, `κ > 4`**, from (G5) alone. -/
theorem separatedTransienceStatement_of_gt_four_of_inverseBoundary {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) : Zhan.SeparatedTransienceStatement.{u} κ :=
  separatedTransienceStatement_of_gt_four_of_clearance hκ4 hG5 (A5Clear.separatedClearanceStatement κ)

/-- **Aux. lemma 7 for `κ > 4`** (Specification §2.2, p. 33) from (G5) alone. -/
theorem aux7Statement_of_gt_four_of_inverseBoundary {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) : Sec4.Aux7Statement.{u} κ :=
  aux7Statement_of_gt_four_of_clearance hκ4 hG5 (A5Clear.separatedClearanceStatement κ)

/-- **Transience for every separated word, every `κ > 0`**, given (G5) when `κ > 4`. -/
theorem separatedTransienceStatement_of_pos_of_inverseBoundary {κ : ℝ} (hκ : 0 < κ)
    (hG5 : 4 < κ → StoppingInverseBoundaryStatement.{0} κ) : Zhan.SeparatedTransienceStatement.{u} κ :=
  separatedTransienceStatement_of_pos_of_clearance hκ fun h4 => ⟨hG5 h4, A5Clear.separatedClearanceStatement κ⟩

/-- **Aux. lemma 7, every `κ > 0`**, given (G5) when `κ > 4`. -/
theorem aux7Statement_of_pos_of_inverseBoundary {κ : ℝ} (hκ : 0 < κ)
    (hG5 : 4 < κ → StoppingInverseBoundaryStatement.{0} κ) : Sec4.Aux7Statement.{u} κ :=
  aux7Statement_of_pos_of_clearance hκ fun h4 => ⟨hG5 h4, A5Clear.separatedClearanceStatement κ⟩

end InteractingSLE.ZhanGT4

namespace InteractingSLE.Sec5

/-- **Zhan's Part A inputs of Section 5 at `16/κ` (clearance form) from (G5) alone**: the clearance half is
`A5Clear.separatedClearanceStatement`. Every consumer of `PartAInputsSixteenDivOfClearance` (`ClearanceWire`) thus needs
only `StoppingInverseBoundaryStatement (16/κ)` for `0 < κ < 4`. -/
theorem partAInputsSixteenDivOfClearance_of_inverseBoundary
    (hG5 : ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.StoppingInverseBoundaryStatement.{0} (16 / κ)) :
    PartAInputsSixteenDivOfClearance :=
  fun κ hκ hκ4 => ⟨hG5 κ hκ hκ4, ZhanGT4.A5Clear.separatedClearanceStatement (16 / κ)⟩

/-- Aux. lemma 7 at `κ′ = 16/κ` from (G5) at `16/κ` alone. -/
theorem aux7Statement_sixteen_div_of_inverseBoundary
    (hG5 : ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.StoppingInverseBoundaryStatement.{0} (16 / κ)) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) : Sec4.Aux7Statement.{v} (16 / κ) :=
  aux7Statement_sixteen_div_of_partA_of_clearance (partAInputsSixteenDivOfClearance_of_inverseBoundary hG5) hκ hκ4

/-- The counterflow restart carrier from the restart law and (G5) at `16/κ` alone. -/
theorem counterflowSegmentRestartStatement_of_restartLaw_of_inverseBoundary
    (hG5 : ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.StoppingInverseBoundaryStatement.{0} (16 / κ))
    (hR : CrossRestart.CounterflowRestartLawStatement.{u}) : CounterflowSegmentRestartStatement.{u} :=
  counterflowSegmentRestartStatement_of_restartLaw_of_partA_of_clearance
    (partAInputsSixteenDivOfClearance_of_inverseBoundary hG5) hR

end InteractingSLE.Sec5
