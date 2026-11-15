/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkAdapt8Transport

/-!
# The canonical transformed noise as a measurable coordinate map

This identifies its values and proves measurability of the coordinate map.
It does not assert any Brownian law.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Adapt8

open Zhan.Retarget

variable {nL j m : ℕ}

/-- The integrated transformed driving equation, as a function of source coordinates. -/
def phiNoise (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + m) → ℝ)
    (p : RCoord nL (j + 1 + m) × ℝ) : ℝ :=
  (phiW κ xL xR ρL ρR p +
      (1 / 2) * (∑ i, LP.retargetρL κ ρL ρR i * (phiVL i p - LP.retargetXL xL xR i)) +
      (1 / 2) * (∑ i, LP.retargetρR ρR i * (phiVR i p - LP.retargetXR xR i))) / Real.sqrt κ

/-- The canonical noise coordinate map is Borel measurable. -/
theorem measurable_phiNoise (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + m) → ℝ) :
    Measurable (phiNoise κ xL xR ρL ρR) := by
  have hW := measurable_phiW κ xL xR ρL ρR
  have hL : ∀ i, Measurable (phiVL (nL := nL) (j := j) (m := m) i) := measurable_phiVL
  have hR : ∀ i, Measurable (phiVR (nL := nL) (j := j) (m := m) i) := measurable_phiVR
  unfold phiNoise
  fun_prop

/-- The canonical transformed noise is exactly its measurable source-coordinate expression. -/
theorem newB_eq_phiNoise {κ : ℝ} {xL ρL : Fin nL → ℝ}
    {xR ρR : Fin (j + 1 + m) → ℝ} {w b : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) {u : ℝ≥0}
    (hs0 : 0 ≤ invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u)
    (hsT : (((invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal : ℝ≥0) : ℝ≥0∞) < T) :
    newB κ xL xR ρL ρR w vL vR u = phiNoise κ xL xR ρL ρR
      (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR
        (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal,
        b (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal) := by
  unfold newB phiNoise
  rw [newW_eq_phiW hp hs0 hsT]
  simp only [newVL_eq_phiVL (b := b) hs0, newVR_eq_phiVR (vL := vL) (b := b) hs0]

end InteractingSLE.Sec5.TwoMark.Adapt8
