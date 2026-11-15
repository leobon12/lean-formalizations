/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LrInj

/-!
# Continuity of the forward run chart at a real point that every piece leaves alive

Packet PROVE-T14-SB2LIFT (round 8; item 1 of handoff §R7.2, run form). For a boundary-walk run with regular launches,
let `x` be a real point such that, up to stage `n`:

* every launched piece has a finite lifetime and leaves `x` alive (`lAlive (stChart (run j)) ⊤ (D j) x`);
* `x` is off the closure of every filled prefix (`x ∉ closure (fill (prefixPhysSet j))`).

Then **`continuousWithinAt_runChart_fwd`**: the forward run chart `(stChart (run n)).1` is continuous within `ℍ` at
`x`, and real there. The proof is an induction over the run:

* a step without a launch recentres the chart by a real number;
* at a launch, the new forward chart is the Loewner forward map composed with the old one. The Loewner map is
  continuous within `ℍ` at the alive real chart point (`continuousWithinAt_fwdMap_real`). The old forward chart maps
  `ℍ` near `x` into `ℍ`, because near `x` the half-plane lies in the old domain `ℍ \ fill (prefix)`, which is the
  inverse chart's image of `ℍ` (`image_runChart_walk_eq`).

With `injAt_of_continuousWithinAt` this gives the one-chart injectivity input of physical aliveness
(`lAlive_iff_notMem_closure_prefix_of_fwd`) at every real point beyond the records.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- **The forward run chart at a real point that every piece leaves alive.** -/
theorem continuousWithinAt_runChart_fwd {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) (x : ℝ) :
    ∀ n, (∀ j < n, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤ ∧ lAlive (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j)) ⊤ (D j) x) →
      (∀ j ≤ n, (x : ℂ) ∉ closure (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D j))) →
      ContinuousWithinAt (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).1 H x ∧
        ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).1 x).im = 0
  | 0, _, _ => by
    have e : stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D 0) = Chart.id.recenter 0 := by
      simp [ExplState.run, ExplState.init, boundaryWalkSpec]
    rw [e]
    refine ⟨(continuous_id.sub continuous_const).continuousWithinAt, ?_⟩
    simp [Chart.id, Chart.recenter]
  | n + 1, hlaunch, hoff => by
    obtain ⟨hc, hre⟩ := continuousWithinAt_runChart_fwd hP x n
      (fun j hj => hlaunch j (Nat.lt_succ_of_lt hj)) (fun j hj => hoff j (Nat.le_succ_of_le hj))
    set spec := boundaryWalkSpec b jumps θ right with hspec
    set s₀ := ExplState.run κ b jumps spec D n with hs₀
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ'⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      show ContinuousWithinAt (ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.1 H x ∧
        ((ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.1 x).im = 0
      rw [ha]
      refine ⟨hc.sub continuousWithinAt_const, ?_⟩
      show ((stChart s₀).1 x - (a : ℂ)).im = 0
      simp [hre]
    · have hlne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by rw [hl]; simp
      obtain ⟨hfinn, halive⟩ := hlaunch n (Nat.lt_succ_self n) hlne
      have hPR := pieceRegular_of_launch hP hlne
      obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
      have hch := chart_launch s₀ n (D n) θ' ⊤ (by rw [min_eq_right le_top]; exact hfinn)
      -- the stopped driver
      have hWc : Continuous (stopDrv ⊤ (D n)) := by
        have h := hPR.continuous_stoppedReal.1
        have e : stopDrv ⊤ (D n) =
            fun r : ℝ => (D n).1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (D n).2).toNNReal := by
          funext r
          simp only [stopDrv, retOf, min_eq_right (le_top : (D n).2 ≤ ⊤)]
        rw [e]
        exact h
      have hT0 : 0 ≤ stopTime ⊤ (D n) := stopTime_nonneg ⊤ (D n)
      -- the alive real chart point
      have hy : (stChart s₀).1 x = (((stChart s₀).1 x).re : ℂ) := Complex.ext (by simp) (by simp [hre])
      obtain ⟨u, hu⟩ := halive
      have hu' : IsForwardSol (stopDrv ⊤ (D n)) ((((stChart s₀).1 x).re : ℝ) : ℂ) (stopTime ⊤ (D n)) u := by
        rw [← hy]
        exact hu
      obtain ⟨hcL, hreL⟩ := continuousWithinAt_fwdMap_real hWc hT0 hu'
      rw [← hy] at hcL hreL
      -- the old forward chart maps `ℍ` near `x` into `ℍ`
      have hfin' : ∀ j < n, (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none → (D j).2 ≠ ⊤ :=
        fun j hj hj' => (hlaunch j (Nat.lt_succ_of_lt hj) hj').1
      have hdom := image_runChart_walk_eq hP hfin'
      obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball (x : ℂ) r ∩ fillH (SB.prefixPhysSet κ b jumps spec D n) = ∅ := by
        have h := isOpen_compl_iff.2 isClosed_closure |>.mem_nhds (hoff n (Nat.le_succ n))
        obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 h
        exact ⟨r, hr, eq_empty_of_forall_notMem fun z hz => hrs hz.1 (subset_closure hz.2)⟩
      have hmaps : MapsTo (stChart s₀).1 (H ∩ ball (x : ℂ) r) H := by
        rintro z ⟨hzH, hzb⟩
        have hzD : z ∈ H \ fillH (SB.prefixPhysSet κ b jumps spec D n) := by
          refine ⟨hzH, fun hzf => ?_⟩
          have : z ∈ ball (x : ℂ) r ∩ fillH (SB.prefixPhysSet κ b jumps spec D n) := ⟨hzb, hzf⟩
          rw [hball] at this
          exact this
        rw [← hdom] at hzD
        obtain ⟨w, hw, rfl⟩ := hzD
        rw [(isConformal_runChart_of_reg spec hP n).2.2 w hw]
        exact hw
      have hcomp : ContinuousWithinAt (fun z => fwdMap (stopDrv ⊤ (D n)) (stopTime ⊤ (D n)) ((stChart s₀).1 z))
          (H ∩ ball (x : ℂ) r) x :=
        hcL.comp (hc.mono inter_subset_left) hmaps
      have hcompH : ContinuousWithinAt
          (fun z => fwdMap (stopDrv ⊤ (D n)) (stopTime ⊤ (D n)) ((stChart s₀).1 z)) H x :=
        (continuousWithinAt_inter (ball_mem_nhds _ hr)).1 hcomp
      show ContinuousWithinAt (ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.1 H x ∧
        ((ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.1 x).im = 0
      rw [he, hch]
      exact ⟨hcompH, hreL⟩

end InteractingSLE.Theorem14.SB.Lk
