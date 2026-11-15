/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvBand

/-!
# Clause (iii) of one sample in the cell-exit frame

Packet PROVE-GW2-BUF (round 19). A target visit of a rightward family in the cell-exit frame
`scaledPath (c₂²) (± c₂) w` at time `t` before `c₂² · τ` is a visit of the sample frame at time `t / λ²` before
`4^k τ`. So J32's reach follows from `ae_reach_of_visit_instX`'s conclusion at the sample.

* **`reach_of_frame_visit`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootN4 GW2JDetR11 GW2Sdy

/-- **Clause (iii) of one sample from the sample frame's reach**: for a rightward family, a target visit in the
cell-exit frame before `c₂² τ` gives the reach, given the reach from every scaled visit before `4^k τ`. -/
theorem reach_of_frame_visit {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q))
    {κ : ℝ} (f : NearCrossingFamily.{u} κ) (hf : f.goLeft = false) (w : ℝ≥0 → ℝ) {τ : ℝ≥0∞} {P : Prop}
    (hvis : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * τ →
      2 + 1 / 8 < (lamL l : ℝ) * ((-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * w (t / (4 : ℝ≥0) ^ r.2))) → P)
    (t : ℝ≥0) (ht : (t : ℝ≥0∞) < ((c2L r l ^ 2 : ℝ≥0) : ℝ≥0∞) * τ)
    (htar : GW2Sdg.imgState f.xL f.xR (scaledPath (c2L r l ^ 2) (nearSign (GW2Sdf.flipOf l.length) * c2L r l) w) t ∈
      nearTarget f) : P := by
  have hl0 : (lamL l : ℝ≥0) ≠ 0 := (lamL_pos l).ne'
  have hl2 : (lamL l ^ 2 : ℝ≥0) ≠ 0 := pow_ne_zero 2 hl0
  have h4 : ((4 : ℝ≥0) ^ r.2 : ℝ≥0) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [GW2Bf.mem_nearTarget_iff f hf] at htar
  refine hvis (t / lamL l ^ 2) ?_ ?_
  · -- the sample time is before `4^k τ`
    have hc : ((c2L r l ^ 2 : ℝ≥0) : ℝ≥0∞) = ((lamL l ^ 2 : ℝ≥0) : ℝ≥0∞) * ((4 : ℝ≥0∞) ^ r.2) := by
      rw [← four_pow_mul_lamL_sq, mul_comm]
      push_cast
      rfl
    rw [hc, mul_assoc] at ht
    rw [ENNReal.coe_div hl2]
    exact ENNReal.div_lt_of_lt_mul' ht
  · -- the value: `(t / λ²) / 4^k = t / c₂²` and `λ (−1)^{|l|} 2^k = ± c₂`
    have htime : t / lamL l ^ 2 / (4 : ℝ≥0) ^ r.2 = t / c2L r l ^ 2 := by
      rw [div_div, mul_comm, four_pow_mul_lamL_sq]
    rw [htime]
    have hval : (lamL l : ℝ) * ((-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * w (t / c2L r l ^ 2))) =
        scaledPath (c2L r l ^ 2) (nearSign (GW2Sdf.flipOf l.length) * c2L r l) w t := by
      unfold scaledPath
      rw [nearSign_flipOf]
      unfold c2L
      push_cast
      ring
    rw [hval]
    exact htar

end InteractingSLE.Theorem14.GW2Bh
