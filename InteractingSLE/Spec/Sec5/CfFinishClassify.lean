/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishValues
import InteractingSLE.Spec.Sec5.CfFinishZero

/-!
# Inverse classification of a separated force word

Packet PROVE-CFCHART2. Every force word with strict side order, zero seed positions,
and nonzero nonseed weights is exactly the angle-zero flow word of some boundary word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfFinish

open Restart Exist.StagedLaw PiecewiseConstantBoundaryData Cond44Ref

/-- Inverse finite-word classification after removal of passive nonseed marks.
The separation and nonzero-weight premises concern the given deterministic word. -/
theorem exists_isFlowType_force {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}
    (hL : StrictAnti vL) (hR : StrictMono vR) (hL0 : vL 0 = 0) (hR0 : vR 0 = 0)
    (hρL : ∀ i : Fin nL, ρL i.succ ≠ 0) (hρR : ∀ j : Fin nR, ρR j.succ ≠ 0) :
    ∃ c : BoundaryWord, FCDet.IsFlowType κ 0 c vL vR ρL ρR := by
  classical
  let F := forceBoundaryData κ ρL ρR vL vR
  let J := forceJumpFinset vL vR
  have hb : IsPiecewiseConstantBoundaryData F J := by
    simpa only [add_zero] using isPiecewiseConstant_forceData κ ρL ρR vL vR 0
  obtain ⟨c, hJ, he⟩ := BoundaryWord.exists_fn_eq hb
  have hlimL : leftLim c.fn = leftLim F := leftLim_congr he
  have hlimR : rightLim c.fn = rightLim F := rightLim_congr he
  have hS : jumpSet c.fn c.jumps = jumpSet F J := by
    rw [hJ]
    exact jumpSet_congr he
  let SL := (jumpSet c.fn c.jumps).filter (· < 0)
  let SR := (jumpSet c.fn c.jumps).filter (0 < ·)
  have hSL : SL = Finset.univ.image (fun i : Fin nL => vL i.succ) := by
    dsimp only [SL]
    rw [hS]
    exact left_jumps_force hκ hL hL0 hρL
  have hSR : SR = Finset.univ.image (fun j : Fin nR => vR j.succ) := by
    dsimp only [SR]
    rw [hS]
    exact right_jumps_force hκ hR hR0 hρR
  have hcL : SL.card = nL := by
    dsimp only [SL]
    rw [hS]
    exact card_left_jumps_force hκ hL hL0 hρL
  have hcR : SR.card = nR := by
    dsimp only [SR]
    rw [hS]
    exact card_right_jumps_force hκ hR hR0 hρR
  have henumL := orderEmb_left_tail hL hSL hcL
  have henumR := orderEmb_right_tail hR hSR hcR
  have eL : flowLineNL c.fn c.jumps 0 = nL + 1 := congrArg (fun k => k + 1) hcL
  have eR : flowLineNR c.fn c.jumps 0 = nR + 1 := congrArg (fun k => k + 1) hcR
  have hLambda : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  refine ⟨c, eL, eR, ?_, ?_, ?_, ?_⟩
  · funext i
    change vL (Fin.cast eL i) =
      Fin.cons (α := fun _ => ℝ) 0 (fun j : Fin SL.card => SL.orderEmbOfFin rfl j.rev - 0) i
    cases i using Fin.cases with
    | zero => exact hL0
    | succ i =>
      have hc : Fin.cast eL i.succ = (Fin.cast hcL i).succ := by apply Fin.ext; rfl
      rw [hc, Fin.cons_succ, sub_zero, henumL i]
  · funext j
    change vR (Fin.cast eR j) =
      Fin.cons (α := fun _ => ℝ) 0 (fun i : Fin SR.card => SR.orderEmbOfFin rfl i - 0) j
    cases j using Fin.cases with
    | zero => exact hR0
    | succ j =>
      have hc : Fin.cast eR j.succ = (Fin.cast hcR j).succ := by apply Fin.ext; rfl
      rw [hc, Fin.cons_succ, sub_zero, henumR j]
  · funext i
    change ρL (Fin.cast eL i) =
      Fin.cons (α := fun _ => ℝ)
        (-(leftLim c.fn 0 + 0 * QuantumZipper.chiC κ) / sleLambda κ - 1)
        (fun j : Fin SL.card =>
          (rightLim c.fn (SL.orderEmbOfFin rfl j.rev) -
            leftLim c.fn (SL.orderEmbOfFin rfl j.rev)) / sleLambda κ) i
    cases i using Fin.cases with
    | zero =>
      change ρL 0 = -(leftLim c.fn 0 + 0 * QuantumZipper.chiC κ) / sleLambda κ - 1
      rw [zero_mul, add_zero, hlimL]
      change ρL 0 = -(leftLim (forceBoundaryData κ ρL ρR vL vR) 0) / sleLambda κ - 1
      rw [leftLim_force_zero κ ρL ρR vL vR hL hL0]
      field_simp
      ring
    | succ i =>
      have hc : Fin.cast eL i.succ = (Fin.cast hcL i).succ := by apply Fin.ext; rfl
      rw [hc, Fin.cons_succ, henumL i, hlimL, hlimR]
      change ρL (Fin.cast hcL i).succ =
        (rightLim (forceBoundaryData κ ρL ρR vL vR) (vL (Fin.cast hcL i).succ) -
          leftLim (forceBoundaryData κ ρL ρR vL vR) (vL (Fin.cast hcL i).succ)) / sleLambda κ
      rw [jump_force_left_succ κ ρL ρR vL vR hL hL0]
      exact (mul_div_cancel_left₀ _ hLambda).symm
  · funext j
    change ρR (Fin.cast eR j) =
      Fin.cons (α := fun _ => ℝ)
        ((rightLim c.fn 0 + 0 * QuantumZipper.chiC κ) / sleLambda κ - 1)
        (fun i : Fin SR.card =>
          (rightLim c.fn (SR.orderEmbOfFin rfl i) -
            leftLim c.fn (SR.orderEmbOfFin rfl i)) / sleLambda κ) j
    cases j using Fin.cases with
    | zero =>
      change ρR 0 = (rightLim c.fn 0 + 0 * QuantumZipper.chiC κ) / sleLambda κ - 1
      rw [zero_mul, add_zero, hlimR]
      change ρR 0 = rightLim (forceBoundaryData κ ρL ρR vL vR) 0 / sleLambda κ - 1
      rw [rightLim_force_zero κ ρL ρR vL vR hR hR0]
      field_simp
      ring
    | succ j =>
      have hc : Fin.cast eR j.succ = (Fin.cast hcR j).succ := by apply Fin.ext; rfl
      rw [hc, Fin.cons_succ, henumR j, hlimL, hlimR]
      change ρR (Fin.cast hcR j).succ =
        (rightLim (forceBoundaryData κ ρL ρR vL vR) (vR (Fin.cast hcR j).succ) -
          leftLim (forceBoundaryData κ ρL ρR vL vR) (vR (Fin.cast hcR j).succ)) / sleLambda κ
      rw [jump_force_right_succ κ ρL ρR vL vR hR hR0]
      exact (mul_div_cancel_left₀ _ hLambda).symm

end InteractingSLE.Sec5.CfFinish
