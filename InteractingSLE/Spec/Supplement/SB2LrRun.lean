/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LrFwd

/-!
# Physical aliveness at a walk launch

Packet PROVE-T14-SB2LIFT (round 8; item 1 of handoff §R7.2 closed for walk runs). For a boundary-walk run with regular
launches, a launch at stage `n` with a finite lifetime, and a real point `x` such that

* every earlier launched piece has a finite lifetime and leaves `x` alive, and `x` is off the closure of every filled
  prefix up to stage `n`;
* the inverse chart has the boundary limit `x` at the chart point `c.1 x` (GW1's `ExteriorInverse` form), and
  `c.1 x ≠ 0` (`x` is not the current point),

**`lAlive_run_iff`** gives `lAlive (stChart (run n)) ⊤ (D n) x ↔ x ∉ closure (fill (prefixPhysSet (n + 1)))`. The new
piece leaves `x` alive iff `x` is physically off the closure of the new filled prefix. The ingredients are:

* the run-chart domain identity at the two stages (`image_runChart_walk_eq`), the launch step through the hull at the
  lifetime (`fwdHull_stopDrv_eq`, `RS.image_fwdMapInv_H`);
* continuity of the forward run chart at `x` (`continuousWithinAt_runChart_fwd`), hence injectivity of the boundary
  map at `c.1 x` (`injAt_of_continuousWithinAt`);
* `lAlive_iff_notMem_closure_prefix_of_fwd`.

No exit classification of the piece (GW1's `ForwardExit`) is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- **The launch step of the domain identity in the launch chart**: at a launch with a finite lifetime, the inverse
chart after the launch maps `ℍ` onto the old inverse chart's image of the complement of the filled closed trace. -/
theorem image_runChart_succ_launch {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) :
    (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1))).2.1 '' H =
      (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).2.1 ''
        (H \ fillH (trOf (D n) '' Icc 0 (D n).2.toNNReal)) := by
  set spec := boundaryWalkSpec b jumps θ right with hspec
  set s₀ := ExplState.run κ b jumps spec D n with hs₀
  have hlne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by rw [hl]; simp
  have hPR := pieceRegular_of_launch hP hlne
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
  rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
  have hch := chart_launch s₀ n (D n) θ' ⊤ (by rw [min_eq_right le_top]; exact hfin)
  have hWc : Continuous (stopDrv ⊤ (D n)) := by
    have h := hPR.continuous_stoppedReal.1
    have e : stopDrv ⊤ (D n) =
        fun r : ℝ => (D n).1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (D n).2).toNNReal := by
      funext r
      simp only [stopDrv, retOf, min_eq_right (le_top : (D n).2 ≤ ⊤)]
    rw [e]
    exact h
  have hW0 : stopDrv ⊤ (D n) 0 = 0 := by
    have h := hPR.continuous_stoppedReal.2
    simpa only [stopDrv, retOf, min_eq_right (le_top : (D n).2 ≤ ⊤)] using h
  have himgL := QuantumZipper.RS.image_fwdMapInv_H hWc hW0 (stopTime_nonneg ⊤ (D n))
  rw [fwdHull_stopDrv_eq hPR hfin] at himgL
  show (ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.2.1 '' H = _
  rw [he, hch, ← himgL, image_image]
  rfl

/-- **Physical aliveness at a walk launch.** -/
theorem lAlive_run_iff {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) (x : ℝ)
    (hlaunch : ∀ j < n, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤ ∧ lAlive (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j)) ⊤ (D j) x)
    (hoff : ∀ j ≤ n, (x : ℂ) ∉ closure (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D j)))
    (hbd : Tendsto (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).2.1
      (𝓝[H] ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).1 x)) (𝓝 (x : ℂ)))
    (hne : (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).1 x ≠ 0) :
    lAlive (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) ⊤ (D n) x ↔
      (x : ℂ) ∉ closure (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1))) := by
  set spec := boundaryWalkSpec b jumps θ right with hspec
  set s₀ := ExplState.run κ b jumps spec D n with hs₀
  have hlne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by rw [hl]; simp
  have hPR := pieceRegular_of_launch hP hlne
  have hcc := isConformal_runChart_of_reg spec hP n
  -- the boundary map of the launch chart
  obtain ⟨hbe, -⟩ := GW1P.isClosed_pieces_run spec D hP n
  obtain ⟨ĝ, C, hf, -⟩ := hbe
  have hĝ : ContinuousOn ĝ {z : ℂ | 0 ≤ z.im} := GW1P.continuousOn_of_tendsto hf
  have hgg : EqOn ĝ (stChart s₀).2.1 H := fun z hz => by
    have : (𝓝[H] z).NeBot := GW1P.neBot_nhdsWithin_H (QuantumZipper.H_subset_Hbar hz)
    exact tendsto_nhds_unique (hf z (QuantumZipper.H_subset_Hbar hz))
      ((hcc.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)
  -- the domain identities
  have hfin' : ∀ j < n, (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none → (D j).2 ≠ ⊤ :=
    fun j hj hj' => (hlaunch j hj hj').1
  have hfin'' : ∀ j < n + 1, (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none → (D j).2 ≠ ⊤ := by
    intro j hj hj'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hfin' j hj hj'
    · exact hfin
  have hD := image_runChart_walk_eq hP hfin'
  have hD' : (stChart s₀).2.1 '' (H \ fillH (trOf (D n) '' Icc 0 (D n).2.toNNReal)) =
      H \ fillH (SB.prefixPhysSet κ b jumps spec D (n + 1)) := by
    rw [← image_runChart_succ_launch hP hl hfin]
    exact image_runChart_walk_eq hP hfin''
  -- the trace is compact
  have hα := isGeneratingTrace_trOf hPR
  have hT : (((D n).2.toNNReal : ℝ≥0) : ℝ≥0∞) = (D n).2 := ENNReal.coe_toNNReal hfin
  have hA : IsCompact (trOf (D n) '' Icc 0 (D n).2.toNNReal) := isCompact_Icc.image_of_continuousOn
    (hα.2.1.mono fun t ht => by rw [← hT]; exact ENNReal.coe_le_coe.2 ht.2)
  -- the forward chart at `x`
  obtain ⟨hfc, hre⟩ := continuousWithinAt_runChart_fwd hP x n hlaunch hoff
  have hyx : ĝ ((stChart s₀).1 x) = x := by
    have hyH : (stChart s₀).1 x ∈ Hbar := show 0 ≤ ((stChart s₀).1 x).im by rw [hre]
    have : (𝓝[H] ((stChart s₀).1 x)).NeBot := GW1P.neBot_nhdsWithin_H hyH
    exact tendsto_nhds_unique (hf _ hyH) hbd
  exact lAlive_iff_notMem_closure_prefix_of_fwd hPR hfin hcc hĝ hgg hD hD' hA (by simp) hre hne hyx hfc
    (hoff n le_rfl)

end InteractingSLE.Theorem14.SB.Lk
