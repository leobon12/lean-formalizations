/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLwChart
import InteractingSLE.Spec.Supplement.WalkIntCanonModelRun
import InteractingSLE.Spec.Supplement.GW1PieceRun

/-!
# B's stage chart has the chart inputs of `Sx.isStageS2_of`

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2`). **`stageChart_facts`**: the run chart of a walk with regular launches
at a stage that is not finished is a domain chart of `ℍ ∖ fill(prefix)`, its forward map is a mapping-out function of
the hull `fill(prefix)` up to a real shift, its lift is the canonical logarithm's imaginary part
(`WalkIntCanon.HullModel` with `IsNormalized`), and its inverse has boundary limits on `ℍ̄` within bounded distance of
the identity (`GW1P.HasProperBdryExt`).
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

open Restart Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The chart inputs of B's stage chart.** -/
theorem stageChart_facts (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) :
    ∃ (s₀ : ℝ) (LY gc : ℂ → ℂ) (Cc : ℝ),
      IsDomainChart (H \ fillH (SB.prefixPhysSet κ b jumps spec D n)) (stChart (ExplState.run κ b jumps spec D n)) ∧
      IsHPHull (fillH (SB.prefixPhysSet κ b jumps spec D n)) ∧
      IsMapOut (fillH (SB.prefixPhysSet κ b jumps spec D n))
        (fun z => (stChart (ExplState.run κ b jumps spec D n)).1 z + (s₀ : ℂ)) ∧
      IsCanonicalDerivLog (fillH (SB.prefixPhysSet κ b jumps spec D n))
        (fun z => (stChart (ExplState.run κ b jumps spec D n)).1 z + (s₀ : ℂ)) LY ∧
      EqOn (stChart (ExplState.run κ b jumps spec D n)).2.2 (fun z => (LY z).im)
        (H \ fillH (SB.prefixPhysSet κ b jumps spec D n)) ∧
      (∀ q ∈ Hbar, Tendsto (stChart (ExplState.run κ b jumps spec D n)).2.1 (𝓝[H] q) (𝓝 (gc q))) ∧
      ∀ q ∈ Hbar, ‖gc q - q‖ ≤ Cc := by
  obtain ⟨M, hM⟩ := Lw.exists_hullModel_fill spec D hreg n hnot
  have hN := WalkIntCanon.isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) spec D n (fun j _ => hreg j)
  have hD := Lw.isDomainChart_runChart spec D hreg n hnot
  have hLY : IsCanonicalDerivLog M.hull (fun z => (stChart (ExplState.run κ b jumps spec D n)).1 z + (M.shift : ℂ))
      (canonDerivLog M.hull) :=
    (isCanonicalDerivLog_canonDerivLog M.isHull).congr M.isHull
      ((ConformalImage.isMapOut_mapOut M.isHull).eqOn M.isHull M.mapOut)
  have hlift := M.lift_eq_canonDerivLog hN
  obtain ⟨gc, Cc, hgc, hCc⟩ := (GW1P.isClosed_pieces_run spec D hreg n).1
  have hY := M.isHull
  have hmap := M.mapOut
  rw [hM] at hLY hlift hY hmap
  exact ⟨M.shift, canonDerivLog (fillH (SB.prefixPhysSet κ b jumps spec D n)), gc, Cc, hD, hY, hmap, hLY, hlift,
    hgc, hCc⟩

end InteractingSLE.Theorem14.SB.Sx
