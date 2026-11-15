/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2ReadoutPiece
import InteractingSLE.Spec.Supplement.WalkUnionLawMain

/-!
# A measurable physical parametrization at each R51 schedule launch

Packet PROVE-T14-SBTAIL2. Apply the interior-chart readout to the regularized
history, and transfer the launched piece back using equality of the retained
driver and the run. The resulting path has measurable coordinates and is
continuous with the exact actual-piece range on the original launch event.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Readout

open Exist.Staged Exist.StagedLaw GW2Schedule

/-- Regularization changes neither the launch chart nor the finite stopped
physical piece when the current original piece is regular through its stop. -/
theorem schedulePiece_regHist_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {Ω : Type u} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {ω : Ω} {k : ℕ} (hk : k < (scheduleProgram 0 l).length)
    (hrun : ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => StagedReg.regHist ⟨x, true, scheduleProgram 0 l⟩ E j ω) k =
      ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ (fun j => E j ω) k)
    (hr : GW1P.PieceRegular (E k ω).1 (min (schedDelta 0 l k) (E k ω).2)) :
    schedulePiece κ b jumps x l
        (fun j => StagedReg.regHist ⟨x, true, scheduleProgram 0 l⟩ E j ω) k =
      schedulePiece κ b jumps x l (fun j => E j ω) k := by
  have ht : instrTime (x, true, scheduleProgram 0 l) k = schedDelta 0 l k := by
    unfold instrTime
    rw [isFlowProg_scheduleProgram 0 l k hk]
  have hcan : canonDrv (schedDelta 0 l k)
      (StagedReg.regHist ⟨x, true, scheduleProgram 0 l⟩ E k ω) =
      canonDrv (schedDelta 0 l k) (E k ω) := by
    change canonDrv (schedDelta 0 l k) (StagedReg.regularize
      (instrTime (x, true, scheduleProgram 0 l) k) (E k ω)) = _
    rw [ht]
    exact StagedReg.canonDrv_regularize hr.1 hr.2.1
  have hdriver := congrArg Prod.fst hcan
  dsimp only [canonDrv] at hdriver
  simp only [StagedReg.regHist_snd] at hdriver
  unfold schedulePiece
  rw [hrun]
  simp only [StagedReg.regHist_snd, hdriver]

/-- The actual piece at every finite schedule launch has a parametrization
with measurable coordinates, under precisely R51's piece regularity and driver
measurability. No field-law or lower-tail assumption is used. -/
theorem exists_measurable_schedulePiece_param {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) :
    ∃ a : Ω → ℝ≥0 → ℂ, (∀ t, Measurable fun ω => a ω t) ∧
      ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
          (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        Continuous (a ω) ∧ range (a ω) = schedulePiece κ b jumps x l (fun j => E j ω) k := by
  let spec : ExplSpec := ⟨x, true, scheduleProgram 0 l⟩
  let E' := StagedReg.regHist spec E
  have hR' := WalkLaw.stagedPiecesRegular_regHist hR
  obtain ⟨M, hMae, hMm, hMp⟩ := hR'.ae_pieceRegular.exists_measurable_mem
  have ht : instrTime spec k = schedDelta 0 l k := by
    unfold instrTime
    rw [isFlowProg_scheduleProgram 0 l k hk]
  obtain ⟨a, ham, ha⟩ := exists_measurable_piece_param hb spec (E := E')
    (StagedReg.measurable_regHist hEm) StagedReg.isRegularDriver_regHist hMm hMp k
    (by rw [ht]; exact schedDelta_ne_top 0 l k)
  refine ⟨a, ham, ?_⟩
  filter_upwards [hMae, StagedReg.ae_run_regHist hR, hR.ae_pieceRegular]
    with ω hωM hrun hωR hl
  have hl' : (ExplState.run κ b jumps spec (fun j => E' j ω) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hrun (k + 1)]
    exact hl
  obtain ⟨hac, har⟩ := ha ω hωM hl'
  have he : range (a ω) = schedulePiece κ b jumps x l (fun j => E' j ω) k := by
    change range (a ω) = (ExplState.run κ b jumps spec (fun j => E' j ω) k).2.2.2.2.1.tipSet
      (fun r : ℝ≥0 => (E' k ω).1 (min (r : ℝ≥0∞) (min (instrTime spec k) (E' k ω).2)).toNNReal)
      (min (instrTime spec k) (E' k ω).2) at har
    rw [ht] at har
    exact har
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hr := hωR k c θ hcθ
  rw [ht] at hr
  exact ⟨hac, he.trans (schedulePiece_regHist_eq hk (hrun k) hr)⟩

end InteractingSLE.Theorem14.SB.Readout
