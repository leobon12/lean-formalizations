/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartPairRecord
import InteractingSLE.Spec.Sec5.GlueCondUnionImg

/-!
# BW2.5: the retargeting map and its inherited derivative lift

The two inversion charts differ by `u ↦ u / (1 + B*u)`. Its logarithm
`-2 Log (1 + B*u)` is zero at the common source and is exactly the difference
of the inherited inversion lifts. No additive phase is chosen again.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW1RestartPair

/-- The counterflow chart transition in BW2.5. -/
def retargetMap (B : ℝ) : ℂ → ℂ := QuantumZipper.CA.realMobius 1 0 B 1

/-- The branch fixed to be real at the common source zero. -/
def retargetLift (B : ℝ) (u : ℂ) : ℂ := -2 * log (1 + B * u)

theorem retargetMap_eq (B : ℝ) (u : ℂ) : retargetMap B u = u / (1 + B * u) := by
  simp only [retargetMap, QuantumZipper.CA.realMobius, ofReal_one, one_mul,
    ofReal_zero, add_zero, add_comm]

/-- BW2.5 holds at every finite point of the two ordinary charts. -/
theorem recenter_inversion_transition (c : Chart) (B : ℝ) {z : ℂ}
    (hz : c.1 z ≠ 0) (hzB : c.1 z - B ≠ 0) :
    ((c.recenter B).trans infinitySourceChart).1 z =
      retargetMap B ((c.trans infinitySourceChart).1 z) := by
  change -(c.1 z - B)⁻¹ = retargetMap B (-(c.1 z)⁻¹)
  rw [retargetMap_eq]
  have hden : 1 + (B : ℂ) * -(c.1 z)⁻¹ ≠ 0 := by
    intro he
    apply hzB
    field_simp at he
    linear_combination he
  have he : 1 + (B : ℂ) * -(c.1 z)⁻¹ = (c.1 z - B) * (c.1 z)⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hz]
    ring
  rw [eq_div_iff hden, he, ← mul_assoc, neg_mul, inv_mul_cancel₀ hzB, neg_one_mul]

/-- The retargeting is an automorphism of the upper half-plane for either side. -/
theorem bijOn_retargetMap (B : ℝ) : BijOn (retargetMap B) H H :=
  QuantumZipper.CA.bijOn_realMobius_H (by simp : (0 : ℝ) < 1 * 1 - 0 * B)

theorem hasDerivAt_retargetMap (B : ℝ) {u : ℂ} (hu : 1 + (B : ℂ) * u ≠ 0) :
    HasDerivAt (retargetMap B) (1 / (1 + B * u) ^ 2) u := by
  simpa only [retargetMap, mul_one, zero_mul, sub_zero, ofReal_one, add_comm] using
    (Sec5.GlueImg.hasDerivAt_realMobius (a := 1) (b := 0) (c := B) (d := 1)
      (by simpa only [ofReal_one, add_comm] using hu))

/-- The common source has positive derivative exactly one. -/
theorem hasDerivAt_retargetMap_zero (B : ℝ) : HasDerivAt (retargetMap B) 1 0 := by
  simpa using hasDerivAt_retargetMap B (u := 0) (by simp)

theorem retargetLift_zero (B : ℝ) : retargetLift B 0 = 0 := by simp [retargetLift]

theorem retarget_denom_mem_slitPlane (B : ℝ) {u : ℂ} (hu : u ∈ H) :
    1 + (B : ℂ) * u ∈ slitPlane := by
  by_cases hB : B = 0
  · simpa only [hB, ofReal_zero, zero_mul, add_zero] using one_mem_slitPlane
  · right
    simpa only [add_im, one_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
      zero_add] using mul_ne_zero hB (ne_of_gt hu)

/-- The analytic logarithm of the transition derivative, with its source branch. -/
theorem isDerivLog_retargetMap (B : ℝ) :
    IsDerivLog (retargetMap B) (retargetLift B) H := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · exact (((differentiableAt_const _).add
      (differentiableAt_id.const_mul (B : ℂ))).clog
      (retarget_denom_mem_slitPlane B hu)).const_mul (-2) |>.differentiableWithinAt
  · have hn := slitPlane_ne_zero (retarget_denom_mem_slitPlane B hu)
    rw [(hasDerivAt_retargetMap B hn).deriv, retargetLift,
      show (-2 : ℂ) * log (1 + B * u) = -((2 : ℕ) * log (1 + B * u)) by ring,
      exp_neg, exp_nat_mul, exp_log hn, one_div]

/-- The inherited inversion logarithms give precisely BW2.5's logarithm.
The difference of two arguments in `(0, π)` lies in the principal strip. -/
theorem inherited_inversion_lifts (B : ℝ) {v : ℂ} (hv : v ∈ H) :
    -2 * log (v - B) - (-2 * log v) = retargetLift B (-v⁻¹) := by
  have hvB : v - B ∈ H := by
    simpa only [H, mem_ofPred_eq, sub_im, ofReal_im, sub_zero] using hv
  have hv0 : v ≠ 0 := DerivLog.ne_zero_of_mem_H hv
  have he : 1 + (B : ℂ) * -v⁻¹ = (v - B) / v := by
    field_simp
    ring
  rw [retargetLift, he, DerivLog.log_div_eq_sub_of_mem_H hvB hv]
  ring

/-- Recentering preserves the ordinary derivative lift literally. -/
theorem recenter_lift (c : Chart) (B : ℝ) : (c.recenter B).2.2 = c.2.2 := rfl

end InteractingSLE.Theorem14.GW1RestartPair
