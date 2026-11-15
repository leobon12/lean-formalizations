/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2PointZero

/-!
# SB4 schedule avoidance needs sewing only for positive stopped duration

The zero-stop case follows from retained-prefix inclusion. The actual
conditional launch word decides the zero/positive lifetime alternative.
The measurable physical-side readout then lifts conditional avoidance to the
original measure. The positive-duration sewing input below remains unproved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Retain

open Leaf Exist.Staged Exist.StagedLaw GW2Schedule

/-- One actual schedule step avoids the physical forbidden side once sewing
has been constructed on its positive-duration conditional branch. The new
input `hpositive` is geometric; this conditional helper is not a source leaf. -/
theorem ae_schedulePiece_avoids_of_positive_tail
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E)
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {specL : ExplSpec} (hELm : ∀ j, Measurable (EL j))
    (hRL : StagedPiecesRegular κ b jumps P specL EL)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length)
    (hprev : ∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E j ω) k ∩
        rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω)) = ∅)
    (hpositive : ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
        0 < min (schedDelta 0 l k) (E k ω).2) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
        ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
          HasActualTailSewing (schedulePiece κ b jumps x l (fun j => E j ω) k)
            (rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω)))) :
    ∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
      schedulePiece κ b jumps x l (fun j => E j ω) k ∩
        rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω)) = ∅ := by
  have hz := ae_zero_stop_avoids_of_prefix hR hk hprev
  by_cases hδ : schedDelta 0 l k = 0
  · exact hz.mono fun ω hω hl => hω hl (by simp only [hδ, zero_min])
  have hδpos : 0 < schedDelta 0 l k := pos_iff_ne_zero.2 hδ
  obtain ⟨a, ham, hareg⟩ := Side.exists_rightSide_launch_param hb hE.1 hR hELm hRL hk
  have hF := measurableSet_launchEvent_schedule (κ := κ) (b := b) (jumps := jumps) (x := x) E hk
  apply ae_of_ae_condExpKernel_of_nullMeasurableSet (hE.2.1 k)
    (nullMeasurableSet_piece_avoidance (hE.2.1 k _ hF).nullMeasurableSet ham hareg)
  filter_upwards [ae_launch_word_cases hκ hb hE hR k, hpositive,
    KernelTower.ae_ae_condExpKernel_of_ae (hE.2.1 k) hz,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (hE.2.1 k) hF.compl]
    with ω₀ hword hpos hzero hnot
  by_cases hl : ω₀ ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k
  · obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    obtain ⟨_, _, _, _, _, _, _, _, hcases⟩ := hword c θ hcθ
    rcases hcases with h0 | hp
    · filter_upwards [hzero, h0] with ω hzω hω hωF
      exact hzω hωF (by rw [hω.1, min_zero])
    · have hstop : ∀ᵐ ω ∂(condExpKernel P
          (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
          0 < min (schedDelta 0 l k) (E k ω).2 :=
        hp.mono fun _ hω => lt_min hδpos hω
      exact (hpos c θ hcθ hstop).mono fun _ hω hωF => (hω hωF).avoids
  · exact (hnot hl).mono fun _ hω hωF => False.elim (hω hωF)

end InteractingSLE.Theorem14.SB.Retain
