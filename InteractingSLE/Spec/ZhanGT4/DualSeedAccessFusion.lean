/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessLog

/-!
# The fused source normalization in the opposite view

Packet PROVE-ZHAN-GT4-A22. All original seed locations coincide at the
first source in the second marginal. Their derivative normalization is
exactly the conformal weight of that amalgamated charge. This proves the
reference generator cancellation without using distinct original marks.
-/

set_option autoImplicit false
noncomputable section
open Finset
namespace InteractingSLE.ZhanGT4

/-- Conformal weights add with the pair interactions when charges fuse. -/
theorem dualGamma_add_sum {n : ℕ} (κ a : ℝ) (r : Fin n → ℝ) :
    dualGamma κ (a + ∑ m, r m) = dualGamma κ a + (∑ m, dualGamma κ (r m)) +
      κ / 2 * a * (∑ m, r m) + pairSum (fun m k => dualDelta κ (r m) (r k)) := by
  have hsum : (∑ m, dualGamma κ (r m)) =
      κ / 4 * (∑ m, r m ^ 2) + (1 - κ / 4) * (∑ m, r m) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by unfold dualGamma; ring
  have hpair : pairSum (fun m k => dualDelta κ (r m) (r k)) =
      pairSum (fun m k => r m * r k) * (κ / 2) := by
    rw [← pairSum_mul_const]
    congr 1
    funext m k
    unfold dualDelta
    ring
  rw [hsum, hpair]
  have hsq := sq_sum_eq_sum_sq_add_pairSum r
  unfold dualGamma
  linear_combination (κ / 4) * hsq

/-- The powers of the original source derivative in the normalized
(D13)--(D15) factors sum to the amalgamated source's conformal weight. -/
theorem dualGamma_seed_fusion {n : ℕ} (κ : ℝ) (r : Fin n → ℝ) :
    dualGamma κ (-1 / 2 + ∑ m, r m) = (3 * κ - 8) / 16 +
      (∑ m, (dualGamma κ (r m) + -(κ / 4) * r m)) +
      pairSum (fun m k => dualDelta κ (r m) (r k)) := by
  have he := dualGamma_add_sum κ (-1 / 2) r
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [he]
  unfold dualGamma
  ring

/-- The one-source reference partition function has zero driftless
exponential generator. This identity needs no nonzero-gap assumption,
although its differential interpretation uses a protected source. -/
theorem fused_source_gen_eq_zero (κ R E : ℝ) :
    (-2 * dualGamma κ R + 2 * R) / E ^ 2 +
      κ / 2 * (-R / E ^ 2 + (R / E) ^ 2) = 0 := by
  unfold dualGamma
  ring

/-- Dividing a zero-generator field by the fused source partition
function gives a zero generator under its actual force drift. -/
theorem fused_quotient_gen_eq_zero {κ R E Ty Xy XXy : ℝ}
    (hy : Ty + κ / 2 * (XXy + Xy ^ 2) = 0) :
    (Ty - (-2 * dualGamma κ R + 2 * R) / E ^ 2) +
      (κ * R / E) * (Xy - R / E) +
      κ / 2 * ((XXy + R / E ^ 2) + (Xy - R / E) ^ 2) = 0 := by
  have hzero := fused_source_gen_eq_zero κ R E
  linear_combination hy - hzero

end InteractingSLE.ZhanGT4
