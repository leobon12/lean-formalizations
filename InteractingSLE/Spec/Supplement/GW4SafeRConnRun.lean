/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRConnStep
import InteractingSLE.Spec.Supplement.GW1WalkExitGeometry

/-!
# GW4: every recorded connector of an extreme walk has the required height

Reuse the ready-state induction for the actual finite walk. Flow instructions
leave its connector list unchanged; continuation instructions preserve the
height invariant by the first-restart rule. At the extreme angles the shifted
bound is exactly the incoming counterflow height bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW4Fix

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish GW1WalkExit GW1WalkChain
open PiecewiseConstantBoundaryData (jumpSet)

/-- The height invariant at every complete round of the finite walk. -/
theorem connectorShiftBounds_rounds {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hreg : ∀ k, IsRegularDriver (D k))
    (hS : WalkStageData κ b J θ right D)
    (hP : ∀ k c θ',
      (ExplState.run κ b J (boundaryWalkSpec b J θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b J θ right) k) (D k).2)) :
    ∀ n ≤ (jumpSet b J).card + 1,
      ConnectorShiftBounds κ θ b J right
        (ExplState.run κ b J (boundaryWalkSpec b J θ right) D (2 * n)) := by
  let spec := boundaryWalkSpec b J θ right
  let R := ExplState.run κ b J spec D
  intro n
  induction n with
  | zero =>
    intro _ a ha
    exact False.elim (List.not_mem_nil ha)
  | succ n ih =>
    intro hn
    have hn' : n ≤ (jumpSet b J).card := by omega
    have hOld := ih (by omega)
    have hc : R (2 * (n + 1)) = ExplState.contStep κ b J (R (2 * n + 1)) none right := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      apply GW1W.run_succ_walk_cont
      · rw [boundaryWalk_length]; omega
      · omega
    change ConnectorShiftBounds κ θ b J right (R (2 * (n + 1)))
    rcases walk_prefix_geometry hκ hb D hreg hS hP n (by omega) with hd | ⟨hr, -, -⟩
    · have hf : R (2 * n + 1) = R (2 * n) := done_run_succ spec D hd
      rw [hc, hf, contStep_of_done hd]
      exact hOld
    · obtain ⟨hlaunch, hl⟩ := launch_at_even_of_launchReady D hn' hr
      change R (2 * n + 1) = ExplState.launch (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤
        at hlaunch
      have hMid : ConnectorShiftBounds κ θ b J right (R (2 * n + 1)) := by
        intro a ha
        rw [hlaunch, GW2aCont.arcs_launch] at ha
        exact hOld a ha
      have hclass := (hS (2 * n) hl).2.2.2
      change ClassifiedExit κ b right (R (2 * n)) (R (2 * n + 1)) at hclass
      rw [hc]
      by_cases hd : stStatus (R (2 * n + 1)) = stDone
      · rw [contStep_of_done hd]
        exact hMid
      · have hout := (hclass.1.resolve_left hd).2
        exact connectorShiftBounds_contStep hb hMid hout (hclass.2 hd)
          (by rw [hlaunch]; exact angle_launch _ _ _ _)

/-- No geometric connector-height premise remains once the existing regular
stage data and ordinary-piece regularity are supplied. -/
theorem walkConnectorHeightBounds_of_stageData {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hreg : ∀ k, IsRegularDriver (D k))
    (hS : WalkStageData κ b J (if right then -(Real.pi / 2) else Real.pi / 2) right D)
    (hP : ∀ k c θ',
      (ExplState.run κ b J (GW1Z.walkSpec b J right) D (k + 1)).2.2.2.1 k =
        some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (GW1Z.walkSpec b J right) k) (D k).2)) :
    WalkConnectorHeightBounds κ b J (GW1Z.walkSpec b J right) D right := by
  have hH := connectorShiftBounds_rounds hκ hb D hreg hS hP
    ((jumpSet b J).card + 1) le_rfl
  rw [← boundaryWalk_length b J (if right then -(Real.pi / 2) else Real.pi / 2) right]
    at hH
  have hΛ := Sec4.sleLambda_sixteen_div_eq_sub hκ
  intro a ha x hx _ hxJ
  have hh := hH a ha x hx hxJ
  cases right
  · change sleLambda κ ≤ b x + Real.pi / 2 * chiC κ at hh
    change sleLambda (16 / κ) ≤ b x
    linarith only [hh, hΛ]
  · change b x + -(Real.pi / 2) * chiC κ ≤ -sleLambda κ at hh
    change b x ≤ -sleLambda (16 / κ)
    linarith only [hh, hΛ]

end InteractingSLE.Theorem14.GW4Fix
