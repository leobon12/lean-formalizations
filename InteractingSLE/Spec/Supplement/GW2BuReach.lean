/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BfNear

/-!
# Reach from a target visit, with the read known only before a stop

Packet PROVE-GW2-BUF (round 18; clause (iii) of `VNearImgOn`). Round 5's `mem_reachSet_of_cross` and
`mem_reachSet_of_scaled_target` take the record's read `S + W` at every live rational time. At a root `x`, ROOTX's
driver identification (`GW2Rv.ae_j32DriverId_schedInstSX`) gives it only below the instance's cap. The successors here
take the read only below a stop `τ ≤` the record's lifetime, which is all the argument uses: a rational time near the
crossing below `τ`.

* **`mem_reachSet_of_cross_before`**, **`mem_reachSet_of_scaled_target_before`**.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open GW2TipSystem GW2TipSystem.RootV7 GW2TipSystem.RootD25 GW2Bf

/-- **Reach from a crossing below a stop**: the read is `S + W` (`W` continuous) at the live rational times below
`τ ≤` the lifetime, and `2 < S + W t` at a real time `t < τ`. -/
theorem mem_reachSet_of_cross_before {z : DriverRecord} {S : ℝ} {W : ℝ≥0 → ℝ} (hW : Continuous W) {τ : ℝ≥0∞}
    (hτ : τ ≤ z.1) (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < τ → z.2 q = S + W q)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) (hcross : 2 < S + W t) : z ∈ reachSet := by
  have hU : IsOpen {s : ℝ≥0 | 2 < S + W s} := isOpen_lt continuous_const (continuous_const.add hW)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU t hcross
  obtain ⟨q, -, hqτ, hqd⟩ := exists_nnrat_near ht hε
  have hqL : ((q : ℝ≥0) : ℝ≥0∞) < z.1 := hqτ.trans_le hτ
  have hq2 : 2 < z.2 q := by
    rw [hread q hqτ]
    exact hball (by rw [Metric.mem_ball, NNReal.dist_eq]; exact hqd)
  change entryCapacity z < z.1
  refine lt_of_le_of_lt (iInf_le _ q) ?_
  rw [ite_eq_left (show ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q from ⟨hqL, hq2⟩)]
  exact hqL

/-- **Reach from a scaled target visit below a stop.** -/
theorem mem_reachSet_of_scaled_target_before {z : DriverRecord} {S lam : ℝ} {W : ℝ≥0 → ℝ} (hW : Continuous W)
    {τ : ℝ≥0∞} (hτ : τ ≤ z.1) (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < τ → z.2 q = S + W q) (hlam : 0 < lam)
    (hS : S < 2 + 1 / 8) (hscale : lam * (2 + 1 / 8 - S) ≤ 2 + 1 / 8) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ)
    (htarget : 2 + 1 / 8 < lam * W t) : z ∈ reachSet := by
  refine mem_reachSet_of_cross_before hW hτ hread ht ?_
  have hpos : 0 < 2 + 1 / 8 - S := by linarith
  have h1 : lam * (2 + 1 / 8 - S) < lam * W t := lt_of_le_of_lt hscale htarget
  have h2 : 2 + 1 / 8 - S < W t := lt_of_mul_lt_mul_left h1 hlam.le
  linarith

end InteractingSLE.Theorem14.GW2Bh
