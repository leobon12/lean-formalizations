import HigherDimLQGMetric.CM.SphereTilt

/-!
# Oscillation of the tilt potential on a small ball (packet W3b, [S] Lemma 2.6, Step 1)

`k = F_{r,z} − F_{R,0}` is the logarithmic potential of `σ_{r,z} − σ_{R,0}` (F4's `sf4Potential`).
By F3, `F_{r,z}(x) = −log r + F₁((x − z)/r)` with `−log(|y| + 1) ≤ F₁(y) ≤ 2^d`. For `r ≤ R`,
`|z| ≤ A R`, `|v|, |u| ≤ 1` the `log r` and `log R` terms cancel in `k(z + r v) − k(z + r u)` and
(`w3b_sf4Potential_sub_le`)

  `k(z + r v) − k(z + r u) ≤ 2·2^d + log 2 + log(A + 2)`;

averaging over `u ∈ ∂B_1` (`w3b_sf4Potential_le_avg_add`): on `B̄_r(z)`, `k ≤ ∫ k dσ_{r,z} + K_A`.
This is MA1 A8's bound `sup_{B_{2t}(z)} |k| = O_L(1)` for the centred potential, in the one-sided
form used by Weyl scaling.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The tilt potential in terms of the unit-sphere potential `F₁ = sphPot d`. -/
theorem w3b_sf4Potential_apply (hd : 2 ≤ d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w x : Rd d) :
    sf4Potential hd hr hρ z w x =
      (-Real.log r + sphPot d (r⁻¹ • (x - z))) - (-Real.log ρ + sphPot d (ρ⁻¹ • (x - w))) := by
  show logPotM (sphMeas r z) x - logPotM (sphMeas ρ w) x = _
  rw [logPotM_sphMeas hd hr, logPotM_sphMeas hd hρ]

/-- The constant `K_A = 2·2^d + log 2 + log(A + 2)` of the oscillation bound. -/
def w3bPotConst (d : ℕ) (A : ℝ) : ℝ := 2 * 2 ^ d + Real.log 2 + Real.log (A + 2)

/-- **Oscillation bound** of the tilt potential: for `r ≤ R`, `|z| ≤ A R`, `|v|, |u| ≤ 1`,
`k(z + r v) − k(z + r u) ≤ K_A`, with `k = F_{r,z} − F_{R,0}`. -/
theorem w3b_sf4Potential_sub_le (hd : 2 ≤ d) {r R A : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    {z : Rd d} (hz : ‖z‖ ≤ A * R) {v u : Rd d} (hv : ‖v‖ ≤ 1) (hu : ‖u‖ ≤ 1) :
    sf4Potential hd hr hR z 0 (z + r • v) - sf4Potential hd hr hR z 0 (z + r • u) ≤
      w3bPotConst d A := by
  rw [w3b_sf4Potential_apply, w3b_sf4Potential_apply]
  have hrv : r⁻¹ • (z + r • v - z) = v := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hru : r⁻¹ • (z + r • u - z) = u := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [hrv, hru, sub_zero, sub_zero]
  -- the four unit-sphere potential bounds
  have h1 : sphPot d v ≤ 2 ^ d := sphPot_le hd v
  have h2 : sphPot d (R⁻¹ • (z + r • u)) ≤ 2 ^ d := sphPot_le hd _
  have h3 : -Real.log (‖u‖ + 1) ≤ sphPot d u := neg_log_le_sphPot hd u
  have h4 : -Real.log (‖R⁻¹ • (z + r • v)‖ + 1) ≤ sphPot d (R⁻¹ • (z + r • v)) :=
    neg_log_le_sphPot hd _
  have h5 : Real.log (‖u‖ + 1) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by linarith)
  have hnorm : ‖R⁻¹ • (z + r • v)‖ ≤ A + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    have hzv : ‖z + r • v‖ ≤ A * R + R := by
      calc ‖z + r • v‖ ≤ ‖z‖ + ‖r • v‖ := norm_add_le _ _
        _ = ‖z‖ + r * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        _ ≤ A * R + R * 1 := by
            have : r * ‖v‖ ≤ R * 1 := mul_le_mul hrR hv (norm_nonneg _) hR.le
            linarith
        _ = A * R + R := by ring
    rw [inv_mul_le_iff₀ hR]
    linarith
  have h6 : Real.log (‖R⁻¹ • (z + r • v)‖ + 1) ≤ Real.log (A + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  unfold w3bPotConst
  linarith

/-- **One-sided bound against the sphere average**: on `B̄_r(z)`, `k ≤ ∫ k dσ_{r,z} + K_A`. -/
theorem w3b_sf4Potential_le_avg_add (hd : 2 ≤ d) {r R A : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hrR : r ≤ R) {z : Rd d} (hz : ‖z‖ ≤ A * R) {v : Rd d} (hv : ‖v‖ ≤ 1) :
    sf4Potential hd hr hR z 0 (z + r • v) ≤
      (∫ u, sf4Potential hd hr hR z 0 (z + r • u) ∂(unitSphereProb d)) + w3bPotConst d A := by
  have hcont : Continuous fun u : Rd d => sf4Potential hd hr hR z 0 (z + r • u) :=
    (sf4Potential hd hr hR z 0).continuous.comp (by fun_prop)
  have hint : Integrable (fun u => sf4Potential hd hr hR z 0 (z + r • u)) (unitSphereProb d) :=
    integrable_unitSphereProb_of_continuous hcont
  have h1 : ∫ _u : Rd d, (sf4Potential hd hr hR z 0 (z + r • v) - w3bPotConst d A)
      ∂(unitSphereProb d) ≤ ∫ u, sf4Potential hd hr hR z 0 (z + r • u) ∂(unitSphereProb d) := by
    refine integral_mono_ae (integrable_const _) hint ?_
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    have := w3b_sf4Potential_sub_le hd hr hR hrR hz hv hu.le
    linarith
  rw [integral_unitSphereProb_const (by omega)] at h1
  linarith

end HigherDimLQGMetric
