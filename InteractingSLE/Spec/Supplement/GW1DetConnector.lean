/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1DetPhysical
import InteractingSLE.Spec.Supplement.GW1PieceRun

/-!
# The exact remaining boundary-image obligation at a walk connector

Packet PROVE-GW1-DET. The chart identity, physical retargeting, attainment,
first-visit order, and the original `ConnectorPhysStatement` are proved here
conditional only on the displayed boundary-image property of the actual walk.
`GW1DetBoundaryWalk` discharges that property using the existing fibre invariant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW1Det

open Exist Exist.Staged Exist.StagedLaw GW1W GW1Path GW1Laws GW1WalkExit

/-- The next launch chart is the post-piece chart recentred at `postShift`.
This also covers an initially inadmissible instruction with no previous launch. -/
theorem next_launch_chart_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} {c : Chart} {θ : ℝ}
    (hc : (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * (n + 1) + 1)).2.2.2.1
      (2 * (n + 1)) = some (c, θ)) :
    c = (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n + 1))).recenter
      (postShift κ b jumps (GW1Z.walkSpec b jumps right) D n) := by
  let spec := GW1Z.walkSpec b jumps right
  have hno : (ExplState.run κ b jumps spec D (2 * n + 1 + 1)).2.2.2.1 (2 * n + 1) = none :=
    GW1RestartPair.noLaunch_walk_odd D n
  obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch spec D hno
  have hidx : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
  rw [hidx] at ha
  have hv : postShift κ b jumps spec D n = a := by
    unfold postShift
    rw [ha]
    simp only [Chart.recenter, sub_sub_cancel, Complex.ofReal_re]
  rw [(eq_launch_of_launches spec D hc).2.2, ha, hv]

/-- The boundary image of a connector, relative to the retained old set.
The new endpoint is in the next union, and any boundary preimage of that union
outside the old set lies in the real interval from `0` to the new target.
This is an object-level geometric predicate, not an existence theorem. -/
def ConnectorBoundaryImage (d : Chart) (A B : Set ℂ) (v : ℝ) : Prop :=
  ∀ f : ℂ → ℂ, (∀ p ∈ Hbar, Tendsto d.2.1 (𝓝[H] p) (𝓝 (f p))) →
    f (v : ℂ) ∈ B ∧ ∀ p ∈ Hbar, f p ∈ B → f p ∈ A ∨
      ∃ x : ℝ, p = (x : ℂ) ∧ ((0 ≤ x ∧ x ≤ v) ∨ (v ≤ x ∧ x ≤ 0))

/-- **Conditional connector theorem.** The only unproved hypothesis is the
explicit boundary-image property for the actual walk. All driver and clock
assertions in the original `ConnectorPhysStatement` are discharged. -/
theorem connectorPhysStatement_of_boundaryImage
    (hboundary : ∀ (κ : ℝ), 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
      IsPiecewiseConstantBoundaryData b jumps →
      ∀ (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞), (∀ k, IsRegularDriver (D k)) →
      WalkStageData κ b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right D →
      (∀ k c θ', (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (k + 1)).2.2.2.1 k =
          some (c, θ') →
        GW1P.PieceRegular (D k).1 (min (instrTime (GW1Z.walkSpec b jumps right) k) (D k).2)) →
      ∀ n : ℕ,
        (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * (n + 1) + 1)).2.2.2.1
          (2 * (n + 1)) ≠ none →
        ConnectorBoundaryImage
          (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n + 1)))
          (SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n + 1))
          (SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right) D (2 * (n + 1)))
          (postShift κ b jumps (GW1Z.walkSpec b jumps right) D n)) :
    ConnectorPhysStatement := by
  intro κ hκ hκ4 b jumps hb right D hreg hstage hpieces n c θ hc U Q hQ hU _hU0 havoid hv hret
  have hlaunch : (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none := by
    rw [hc]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  have hboundary' := hboundary κ hκ hκ4 b jumps hb right D hreg hstage hpieces n hlaunch
  have hd := (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps)
    (GW1Z.walkSpec b jumps right) D hpieces (2 * n + 1)).1
  obtain ⟨f, C, hf, hC⟩ := hd
  obtain ⟨hend, hpre⟩ := hboundary' f hf
  obtain ⟨T, hTv, hTB, htip⟩ := firstTipTime_connector_of_preimage hf hC hQ hv havoid hend hpre
  obtain ⟨ℓ, hℓc, hℓm, hℓr, hℓtip⟩ := hret.2
  refine ⟨ℓ, T, hTB, ⟨_, hend, htip⟩, hℓc, hℓm, ?_, ?_⟩
  · rw [hTv] at hℓr
    simpa only [ENNReal.coe_lt_coe, Set.Iio] using hℓr
  · intro r z
    rw [next_launch_chart_eq hc]
    exact isRetargetOf_tipAt_trans ⟨f, C, hf, hC⟩ hQ hU hret hℓtip r z

end InteractingSLE.Theorem14.GW1Det
