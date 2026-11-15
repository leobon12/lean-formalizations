/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitGeometry

/-! # GW1: the per-piece record bounds and the exterior-record charts of the whole walk -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish GW1WalkChain GW1Bookkeep
open PiecewiseConstantBoundaryData (jumpSet)

theorem walk_recordGeometry {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hreg : ∀ k, IsRegularDriver (D k))
    (hS : WalkStageData κ b jumps θ right D)
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)) :
    PieceRealRecordBound κ b jumps θ right D ∧
      (∀ k, let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (R (k + 1)).2.2.2.1 k ≠ none →
          ExteriorRecord right (R k) ∧ ((D k).2 ≠ ⊤ → ExteriorRecord right (R (k + 1)))) := by
  let spec := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps spec D
  have hPrefix := walk_prefix_geometry hκ hb D hreg hS hP
  have hOld (k : ℕ) (hl : (R (k + 1)).2.2.2.1 k ≠ none) :
      RawRecordBound right 0 (R k) ∧ ExteriorInverse right (R k) := by
    obtain ⟨hev, hk⟩ := GW1W.even_of_launches_walk hl
    have hn : k / 2 ≤ (jumpSet b jumps).card + 1 := by
      rw [boundaryWalk_length] at hk
      omega
    have heq : 2 * (k / 2) = k := by omega
    have hi : stStatus (R k) = stDone ∨
        (LaunchReady κ b θ right (R k) ∧ RawRecordBound right 0 (R k) ∧
          ExteriorInverse right (R k)) := by
      simpa only [heq] using hPrefix (k / 2) hn
    rcases hi with hd | ⟨-, hB, hI⟩
    · exact False.elim ((hS k hl).2.1.not_done hd)
    · exact ⟨hB, hI⟩
  have hFinite (k : ℕ) (hl : (R (k + 1)).2.2.2.1 k ≠ none) (hfin : (D k).2 ≠ ⊤) :
      FiniteLaunchData right 0 (R k) k (D k) θ := by
    obtain ⟨hs, hr, hg, hC⟩ := hS k hl
    have he : R (k + 1) = ExplState.launch (R k) k (D k) θ ⊤ := GW1W.launch_walk hl
    have hC' : ClassifiedExit κ b right (R k) (ExplState.launch (R k) k (D k) θ ⊤) := by
      rw [← he]
      exact hC
    exact finiteLaunchData (hOld k hl).1 (hOld k hl).2 hs hr k (hreg k)
      (pieceRegular_walk_of_launch hP hl) (hg hfin) hfin hC' (GW1Z.chartFiber_run spec D hP k)
  have hB := hasBdryLimits_chart_run spec D hP
  constructor
  · intro k c θ'
    dsimp only
    intro hl hnot x hx
    have hln : (R (k + 1)).2.2.2.1 k ≠ none := by rw [hl]; exact Option.some_ne_none _
    have he : R (k + 1) = ExplState.launch (R k) k (D k) θ ⊤ := GW1W.launch_walk hln
    have hfin : (D k).2 ≠ ⊤ := by
      intro ht
      apply hnot
      change stStatus (R (k + 1)) = stDone
      rw [he]
      exact (launch_eq_of_top _ _ _ _ _ (by rw [ht]; exact min_self _)).2.2.2.2.1
    obtain ⟨-, -, hc⟩ := eq_launch_of_launches spec D hl
    have htime := instrTime_walk_of_launch hln
    have hGeo := hFinite k hln hfin
    have hbound := hGeo.piece x (by
      simpa only [hc, htime, min_eq_right le_top] using hx)
    change sideCoord right x ≤ sideCoord right (stPt (R (k + 1)))
    rw [he, hGeo.point]
    exact hbound
  · intro k
    dsimp only
    intro hl
    obtain ⟨hs, hr, -, -⟩ := hS k hl
    refine ⟨exteriorRecord_of_profile_inverse (hB k) hs hr.point_eq (hOld k hl).2, ?_⟩
    intro hfin
    have hGeo := hFinite k hl hfin
    have he : R (k + 1) = ExplState.launch (R k) k (D k) θ ⊤ := GW1W.launch_walk hl
    have hB' : HasBdryLimits (stChart (ExplState.launch (R k) k (D k) θ ⊤)).2.1 := by
      rw [← he]
      exact hB (k + 1)
    change ExteriorRecord right (R (k + 1))
    rw [he]
    exact exteriorRecord_of_profile_inverse hB' hGeo.profile hGeo.point hGeo.inverse

end InteractingSLE.Theorem14.GW1WalkExit
