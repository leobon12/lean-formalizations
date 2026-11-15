/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitFinite
import InteractingSLE.Spec.Supplement.GW1WalkExitCollar

/-!
# GW1: induction of the physical record and the exterior inverse correspondence

At a finite launch, the fibre theorem excludes every real contact beyond the updated
record. At a connector, the new record is the selected original mark and the inverse
correspondence is preserved by the literal real translation of the retained chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish GW1WalkChain GW1Bookkeep
open PiecewiseConstantBoundaryData (jumpSet)

theorem instrTime_walk_of_launch {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) :
    instrTime (boundaryWalkSpec b jumps θ right) k = ⊤ := by
  obtain ⟨hev, hk⟩ := GW1W.even_of_launches_walk hl
  unfold instrTime
  rw [GW1Conn.getElem?_boundaryWalkSpec, ite_eq_left hk, ite_eq_left hev]

theorem pieceRegular_walk_of_launch {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    {k : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) :
    GW1P.PieceRegular (D k).1 (D k).2 := by
  obtain ⟨⟨c, θ'⟩, hc⟩ := Option.ne_none_iff_exists'.1 hl
  simpa only [instrTime_walk_of_launch hl, min_eq_right le_top] using hP k c θ' hc

theorem walk_prefix_geometry {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hreg : ∀ k, IsRegularDriver (D k))
    (hS : WalkStageData κ b jumps θ right D)
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)) :
    ∀ n ≤ (jumpSet b jumps).card + 1,
      let s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n)
      stStatus s = stDone ∨
        (LaunchReady κ b θ right s ∧ RawRecordBound right 0 s ∧ ExteriorInverse right s) := by
  let spec := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps spec D
  have hcont (n : ℕ) (hn : n ≤ (jumpSet b jumps).card) :
      R (2 * (n + 1)) = ExplState.contStep κ b jumps (R (2 * n + 1)) none right := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    apply GW1W.run_succ_walk_cont
    · rw [boundaryWalk_length]; omega
    · omega
  intro n
  induction n with
  | zero =>
    intro _
    exact Or.inr ⟨Or.inl rfl, rawRecordBound_init right 0, exteriorInverse_init right 0⟩
  | succ n ih =>
    intro hn
    change stStatus (R (2 * (n + 1))) = stDone ∨
      (LaunchReady κ b θ right (R (2 * (n + 1))) ∧
        RawRecordBound right 0 (R (2 * (n + 1))) ∧
        ExteriorInverse right (R (2 * (n + 1))))
    have hn' : n ≤ (jumpSet b jumps).card := by omega
    have hc := hcont n hn'
    rcases ih (by omega) with hd | ⟨hready, hOld, hInv⟩
    · have hf : R (2 * n + 1) = R (2 * n) := done_run_succ spec D hd
      exact Or.inl (by rw [hc, hf, contStep_of_done hd]; exact hd)
    · obtain ⟨hlaunch, hl⟩ := launch_at_even_of_launchReady D hn' hready
      change R (2 * n + 1) = ExplState.launch (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ at hlaunch
      obtain ⟨hs, hr, hgood, hclass⟩ := hS (2 * n) hl
      change ClassifiedExit κ b right (R (2 * n)) (R (2 * n + 1)) at hclass
      rcases hclass.1 with hd | ⟨-, hOut⟩
      · exact Or.inl (by rw [hc, contStep_of_done hd]; exact hd)
      · have hnot : stStatus (R (2 * n + 1)) ≠ stDone := by
          cases right <;> rcases hOut with h | ⟨h, -⟩ <;> rw [h] <;> intro he <;> cases he
        have hfin : (D (2 * n)).2 ≠ ⊤ := by
          intro ht
          apply hnot
          rw [hlaunch]
          exact (launch_eq_of_top _ _ _ _ _ (by rw [ht]; exact min_self _)).2.2.2.2.1
        have hF : GW1Z.FiberGood (stChart (R (2 * n))) (statePhysicalSet 0 (R (2 * n))) :=
          GW1Z.chartFiber_run spec D hP (2 * n)
        have hC : ClassifiedExit κ b right (R (2 * n))
            (ExplState.launch (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤) := by
          rw [← hlaunch]
          exact hclass
        have hGeo := finiteLaunchData hOld hInv hs hr (2 * n) (hreg (2 * n))
          (pieceRegular_walk_of_launch hP hl) (hgood hfin) hfin hC hF
        have hbnd : RawRecordBound right 0 (R (2 * n + 1)) := by
          rw [hlaunch]; exact hGeo.raw
        have hinv : ExteriorInverse right (R (2 * n + 1)) := by
          rw [hlaunch]; exact hGeo.inverse
        have hangle : stAngle (R (2 * n + 1)) = θ := by
          rw [hlaunch]; exact angle_launch _ _ _ _
        have hNext := contStep_launchReady_or_done hκ hb hOut (hclass.2 hnot) hangle
        rw [← hc] at hNext
        rcases hNext with hd | hready'
        · exact Or.inl hd
        · rcases contStep_outward_cases (jumps := jumps) hOut with ⟨w, -, he⟩ | he
          · have hm : R (2 * (n + 1)) =
                ExplState.moveAlong (R (2 * n + 1)) right w true := hc.trans he
            exact Or.inr ⟨hready', by rw [hm]; exact rawRecordBound_moveAlong hbnd w,
              by rw [hm]; exact exteriorInverse_moveAlong hinv w⟩
          · exact Or.inl (by rw [hc, he]; cases R (2 * n + 1); rfl)

end InteractingSLE.Theorem14.GW1WalkExit
