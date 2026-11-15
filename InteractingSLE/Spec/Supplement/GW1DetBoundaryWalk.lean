/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1DetBoundary

/-! # The connector boundary image for both actual walks (PROVE-GW1-DET) -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1Det

open Exist Exist.Staged Exist.StagedLaw GW1W GW1Path GW1Laws GW1WalkExit GW1WalkFinish
  GW1Bookkeep PiecewiseConstantBoundaryData

/-- Appending just one connector appends its physical real interval to the
recorded union. -/
theorem statePhysicalSet_eq_union_of_arcs {s₁ s₂ : ExplState} {I : Set ℝ}
    (hp : s₂.1 = s₁.1) (ha : s₂.2.1 = s₁.2.1 ++ [I]) :
    statePhysicalSet 0 s₂ = statePhysicalSet 0 s₁ ∪ ((↑) : ℝ → ℂ) '' I := by
  ext z
  simp only [statePhysicalSet, hp, ha, mem_union, mem_iUnion, exists_prop, List.mem_append,
    List.mem_singleton, or_and_right, exists_or, exists_eq_left]
  exact or_assoc.symm

/-- The existing exterior-record and fibre invariants prove the exact
boundary-image property at every next launch of either walk. -/
theorem connectorBoundaryImage_walk {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hreg : ∀ k, IsRegularDriver (D k))
    (hS : WalkStageData κ b jumps θ right D)
    (hP : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    {n : ℕ} (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none) :
    ConnectorBoundaryImage
      (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n + 1)))
      (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n + 1))
      (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * (n + 1)))
      (postShift κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
  let spec := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps spec D
  have hlen := (even_of_launches_walk hk).2
  rw [boundaryWalk_length] at hlen
  have hn : n < (jumpSet b jumps).card := by omega
  have hl := GW1LaunchClock.previous_launch_of_next hκ hb D hreg hS hP hn hk
  have hcont : R (2 * (n + 1)) = ExplState.contStep κ b jumps (R (2 * n + 1)) none right := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    exact run_succ_walk_cont (by rw [boundaryWalk_length]; omega) (by omega)
  have hnd : stStatus (R (2 * n + 1)) ≠ stDone := by
    intro hd
    apply (hS (2 * (n + 1)) hk).2.1.not_done
    change stStatus (R (2 * (n + 1))) = stDone
    rw [hcont, GW1WalkChain.contStep_of_done hd]
    exact hd
  have hrun1 : R (2 * n + 1) = ExplState.launch (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ :=
    launch_walk hl
  have hfin : (D (2 * n)).2 ≠ ⊤ := by
    intro htop
    apply hnd
    rw [hrun1]
    exact (launch_eq_of_top _ _ _ _ _ (by rw [htop]; exact min_self _)).2.2.2.2.1
  have hE : ExteriorRecord right (R (2 * n + 1)) :=
    ((walk_recordGeometry hκ hb D hreg hS hP).2 (2 * n) hl).2 hfin
  have hB : HasBdryLimits (stChart (R (2 * n + 1))).2.1 := hasBdryLimits_chart_run spec D hP _
  have hF : GW1Z.FiberGood (stChart (R (2 * n + 1))) (statePhysicalSet 0 (R (2 * n + 1))) :=
    GW1Z.chartFiber_run spec D hP _
  have hpieces : (R (2 * (n + 1))).1 = (R (2 * n + 1)).1 := by
    have h := GW1P.pieces_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D
      (GW1RestartPair.noLaunch_walk_odd D n)
    simpa only [show 2 * n + 1 + 1 = 2 * (n + 1) by omega] using h
  have hclass : ClassifiedExit κ b right (R (2 * n)) (R (2 * n + 1)) := (hS (2 * n) hl).2.2.2
  have hang : stAngle (R (2 * n + 1)) = θ := by rw [hrun1]; exact angle_launch _ _ _ _
  change ConnectorBoundaryImage (stChart (R (2 * n + 1))) (statePhysicalSet 0 (R (2 * n + 1)))
    (statePhysicalSet 0 (R (2 * (n + 1)))) (postShift κ b jumps spec D n)
  cases right
  · obtain ⟨hw, -, hc, ha⟩ := connector_left hb hl hk hclass hang
    change stPt (R (2 * (n + 1))) < stPt (R (2 * n + 1)) at hw
    have hv : postShift κ b jumps spec D n = rProf (stChart (R (2 * n + 1)))
        (stPt (R (2 * (n + 1)))) := by
      unfold postShift
      change ((stChart (R (2 * n + 1))).1 0 - (stChart (R (2 * (n + 1)))).1 0).re = _
      change stChart (R (2 * (n + 1))) = _ at hc
      rw [hc]
      simp only [Chart.recenter, R, spec, sub_sub_cancel, Complex.ofReal_re]
    rw [hv]
    obtain ⟨hwend, hI⟩ := inverse_interval_left hE hB hw
    apply connectorBoundaryImage_of_inverse hF (statePhysicalSet_eq_union_of_arcs hpieces ha)
      (left_mem_Icc.2 hw.le) hwend
    intro x hx
    obtain ⟨a, ha', hax⟩ := hI x hx
    exact ⟨a, Or.inr ha', hax⟩
  · obtain ⟨hw, -, hc, ha⟩ := connector_right hb hl hk hclass hang
    change stPt (R (2 * n + 1)) < stPt (R (2 * (n + 1))) at hw
    have hv : postShift κ b jumps spec D n = rProf (stChart (R (2 * n + 1)))
        (stPt (R (2 * (n + 1)))) := by
      unfold postShift
      change ((stChart (R (2 * n + 1))).1 0 - (stChart (R (2 * (n + 1)))).1 0).re = _
      change stChart (R (2 * (n + 1))) = _ at hc
      rw [hc]
      simp only [Chart.recenter, R, spec, sub_sub_cancel, Complex.ofReal_re]
    rw [hv]
    obtain ⟨hwend, hI⟩ := inverse_interval_right hE hB hw
    apply connectorBoundaryImage_of_inverse hF (statePhysicalSet_eq_union_of_arcs hpieces ha)
      (right_mem_Icc.2 hw.le) hwend
    intro x hx
    obtain ⟨a, ha', hax⟩ := hI x hx
    exact ⟨a, Or.inl ha', hax⟩

/-- **The original connector statement, unconditionally.** -/
theorem connectorPhysStatement : GW1Path.ConnectorPhysStatement := by
  apply connectorPhysStatement_of_boundaryImage
  intro κ hκ _hκ4 b jumps hb right D hreg hS hP n hk
  exact connectorBoundaryImage_walk hκ hb D hreg hS hP hk

end InteractingSLE.Theorem14.GW1Det
