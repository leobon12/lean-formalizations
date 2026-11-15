/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YgChart
import InteractingSLE.Spec.Supplement.SB2MkFill
import InteractingSLE.Spec.Supplement.SBS3LtCap

/-!
# The post-head chart is the capped run's chart

Packet PROVE-T14-SB2LIFT (round 33, D51 item 3). For a launch of the boundary walk at stage `n` and an own time
`τ < ζ_n`, the walk capped at `τ` (`WalkSide.capSpec`) is a regular program, unfinished after its last instruction,
whose chart is B's stage chart followed by the Loewner map of the piece stopped at `τ`:

* `headDrv e τ`, `headTime e τ`: the piece's driver stopped at `τ` and the stop time (the bodies of `Mi.sb2StopDrv`,
  `Mi.sb2StopTime`);
* **`cap_chart_facts`**: the post-head chart `(stage chart).loewner (headDrv e τ) (headTime e τ)` is a domain chart of
  `ℍ ∖ fill (P_n ∪ gc(α[0, τ]))` with mapping-out forward map up to a shift, canonical lift, and inverse boundary
  limits within bounded distance (`Sx.stageChart_facts` for the capped program, CORNER's `prefixPhysSet_capSpec_succ`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide GW1Bookkeep Lk LuM

/-- The piece's driver stopped at `τ` (the body of `Mi.sb2StopDrv`). -/
def headDrv (e : (ℝ≥0 → ℝ) × ℝ≥0∞) (τ : ℝ≥0) : ℝ → ℝ := fun x : ℝ =>
  e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) e.2)).toNNReal

/-- The stop time `min τ ζ` as a real number (the body of `Mi.sb2StopTime`). -/
def headTime (e : (ℝ≥0 → ℝ) × ℝ≥0∞) (τ : ℝ≥0) : ℝ := ((min (τ : ℝ≥0∞) e.2).toNNReal : ℝ)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The post-head chart's chart facts.** -/
theorem cap_chart_facts {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c₀ : Chart} {θ' : ℝ}
    (hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c₀, θ'))
    {gc : ℂ → ℂ} (hgcc : ContinuousOn gc Hbar)
    (hgi : EqOn gc (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1 H)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < (D n).2) :
    ∃ (s₀ : ℝ) (LY gcc : ℂ → ℂ) (Ccc : ℝ),
      IsDomainChart (H \ fillH (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∪
          gc '' (trOf (D n) '' Icc 0 τ)))
        ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).loewner (headDrv (D n) τ)
          (headTime (D n) τ)) ∧
      IsHPHull (fillH (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∪
          gc '' (trOf (D n) '' Icc 0 τ))) ∧
      IsMapOut (fillH (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∪
          gc '' (trOf (D n) '' Icc 0 τ)))
        (fun z => ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).loewner
          (headDrv (D n) τ) (headTime (D n) τ)).1 z + (s₀ : ℂ)) ∧
      IsCanonicalDerivLog (fillH (statePhysicalSet 0
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∪ gc '' (trOf (D n) '' Icc 0 τ)))
        (fun z => ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).loewner
          (headDrv (D n) τ) (headTime (D n) τ)).1 z + (s₀ : ℂ)) LY ∧
      EqOn ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).loewner
          (headDrv (D n) τ) (headTime (D n) τ)).2.2 (fun z => (LY z).im)
        (H \ fillH (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∪
          gc '' (trOf (D n) '' Icc 0 τ))) ∧
      (∀ q ∈ Hbar, Tendsto ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).loewner
          (headDrv (D n) τ) (headTime (D n) τ)).2.1 (𝓝[H] q) (𝓝 (gcc q))) ∧
      ∀ q ∈ Hbar, ‖gcc q - q‖ ≤ Ccc := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  have hlne : (ExplState.run κ b jumps w D (n + 1)).2.2.2.1 n ≠ none := by rw [hl']; simp
  obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hlne
  have hℓ : n ≤ w.2.2.length := hlen.le
  have htop : instrTime w n = ⊤ := Lx.instrTime_boundaryWalk_of_launch hl'
  have hwθ : w.2.2[n]? = some (Sum.inl (θ, ⊤)) := by
    rw [hw, GW1Conn.getElem?_boundaryWalkSpec]
    simp [hlen, hev]
  set sc := capSpec w n θ (τ : ℝ≥0∞) with hsc
  -- regularity of the capped program
  have hreg : ∀ k c θ'', (ExplState.run κ b jumps sc D (k + 1)).2.2.2.1 k = some (c, θ'') →
      GW1P.PieceRegular (D k).1 (min (instrTime sc k) (D k).2) := by
    intro k c θ'' hlk
    rcases lt_trichotomy k n with hkn | rfl | hkn
    · rw [run_capSpec_of_le hℓ D (Nat.succ_le_of_lt hkn)] at hlk
      rw [instrTime_capSpec_of_lt hkn hℓ]
      exact hP k c θ'' hlk
    · rw [instrTime_capSpec hℓ]
      have h := hP k c₀ θ' hl'
      rw [htop] at h
      obtain ⟨h0, hc, η, hη, -⟩ := h
      have hle : min (τ : ℝ≥0∞) (D k).2 ≤ min ⊤ (D k).2 := min_le_min_right _ le_top
      refine ⟨h0, hc.mono fun s hs => (show (s : ℝ≥0∞) ≤ _ from hs).trans hle,
        η, BRLeaf.isGeneratingTrace_of_le hη hle, fun htop' => ?_⟩
      exact absurd htop' (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
    · obtain ⟨hk, -, -⟩ := eq_launch_of_launches sc D hlk
      rw [hsc, capSpec_getElem?_of_gt hkn hℓ] at hk
      cases hk
  have hnot := Mk.stStatus_capSpec_ne_done (κ := κ) (b := b) (jumps := jumps) hℓ hwθ D hlne hτ
  -- the chart and the prefix
  have hchart := chart_run_capSpec_succ (κ := κ) (b := b) (jumps := jumps) hℓ hwθ D hl' τ
  have hPR : GW1P.PieceRegular (D n).1 (D n).2 := by
    have h := hP n c₀ θ' hl'
    rwa [htop, min_eq_right le_top] at h
  have hc₀ : c₀ = stChart (ExplState.run κ b jumps w D n) := (eq_launch_of_launches w D hl').2.2
  have hgi' : EqOn gc c₀.2.1 H := by rw [hc₀]; exact hgi
  have hpre := S3.Asm.prefixPhysSet_capSpec_succ hl' hgcc hgi' (isGeneratingTrace_trOf hPR) hPR.1 hPR.2.1 hτ
  obtain ⟨s₀, LY, gcc, Ccc, hD, hY, hmo, hLY, hl, hlim, hC⟩ := stageChart_facts sc D hreg (n + 1) hnot
  have hchart' : stChart (ExplState.run κ b jumps sc D (n + 1)) =
      (stChart (ExplState.run κ b jumps w D n)).loewner (headDrv (D n) τ) (headTime (D n) τ) := hchart
  rw [hchart'] at hD hmo hLY hl hlim
  rw [hpre] at hD hY hmo hLY hl
  exact ⟨s₀, LY, gcc, Ccc, hD, hY, hmo, hLY, hl, hlim, hC⟩

end InteractingSLE.Theorem14.SB.Sx
