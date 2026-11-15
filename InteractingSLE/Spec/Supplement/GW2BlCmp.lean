/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterScale
import InteractingSLE.Spec.Sec5.Prop59NodeTreeFlow

/-!
# Relative gaps are comparison gaps: restart at the stage start and Brownian scaling (D12 items 1–2)

Packet PROVE-GW2-BUF (round 9). The near comparison driver is the relative driver `R` restarted at the stage start
`S` (`shiftDrv R S`) and scaled by `b = 2^{r.2} λ` (`scD b`). A relative label `x` at relative time `S + u` is the
comparison label `b · (rightImg R x S − R S)` at comparison time `b² u`. Its gap to the driver is scaled by `b`:

* **`gap_cmp_eq`**: `rightImg (scD b (shiftDrv R S)) (b (rightImg R x S − R S)) (b² u) − scD b (shiftDrv R S) (b² u)
  = b (rightImg R x (S + u) − R (S + u))` (from `Prop59NodeTree.rightImg_shiftDrv` and
  `StagedRepLater.rightImg_scale`);
* **`collision_cmp_iff`**: a relative collision is a comparison collision; **`gap_cmp_le_iff`**: a relative gap `≤ g/b`
  is a comparison gap `≤ g`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow Sec5.Prop59NodeTree Sec5.CrossCond.StagedRepLater

variable {R : ℝ → ℝ}

theorem scD_shiftDrv_apply {S b : ℝ} (hb : b ≠ 0) (u : ℝ) :
    scD b (shiftDrv R S) (b ^ 2 * u) = b * (R (S + u) - R S) := by
  unfold scD shiftDrv
  rw [mul_div_cancel_left₀ u (pow_ne_zero 2 hb)]

/-- **The comparison gap is the scaled relative gap.** -/
theorem gap_cmp_eq (hR : Continuous R) {S : ℝ} (hS : 0 ≤ S) {b : ℝ} (hb : 0 < b) (x : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    rightImg (scD b (shiftDrv R S)) (b * (rightImg R x S - R S)) (b ^ 2 * u) - scD b (shiftDrv R S) (b ^ 2 * u) =
      b * (rightImg R x (S + u) - R (S + u)) := by
  rw [rightImg_scale (continuous_shiftDrv hR S) hb _ hu, rightImg_shiftDrv hR hS hu x,
    scD_shiftDrv_apply hb.ne' u]
  ring

/-- **A relative collision is a comparison collision.** -/
theorem collision_cmp_iff (hR : Continuous R) {S : ℝ} (hS : 0 ≤ S) {b : ℝ} (hb : 0 < b) (x : ℝ) {u : ℝ}
    (hu : 0 ≤ u) :
    rightImg (scD b (shiftDrv R S)) (b * (rightImg R x S - R S)) (b ^ 2 * u) = scD b (shiftDrv R S) (b ^ 2 * u) ↔
      rightImg R x (S + u) = R (S + u) := by
  have h := gap_cmp_eq hR hS hb x hu
  constructor
  · intro h1
    rw [h1, sub_self] at h
    have h2 : rightImg R x (S + u) - R (S + u) = 0 := by
      rcases mul_eq_zero.1 h.symm with h3 | h3
      · exact absurd h3 hb.ne'
      · exact h3
    linarith
  · intro h1
    rw [h1, sub_self, mul_zero] at h
    linarith

/-- **A small relative gap is a small comparison gap.** -/
theorem gap_cmp_le_iff (hR : Continuous R) {S : ℝ} (hS : 0 ≤ S) {b : ℝ} (hb : 0 < b) (x : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (g : ℝ) :
    rightImg (scD b (shiftDrv R S)) (b * (rightImg R x S - R S)) (b ^ 2 * u) - scD b (shiftDrv R S) (b ^ 2 * u) ≤ g ↔
      rightImg R x (S + u) - R (S + u) ≤ g / b := by
  rw [gap_cmp_eq hR hS hb x hu, le_div_iff₀ hb, mul_comm]

end InteractingSLE.Theorem14.GW2Bh
