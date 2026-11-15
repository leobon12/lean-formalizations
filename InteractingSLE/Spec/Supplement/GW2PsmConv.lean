/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmClaimS

/-!
# GW2's open lines: converting the prefix version's stage-start pairing to the current instance's

Packet PROVE-GW2-STAGEMEAN, R121 round (Claim(k) step, per sample, deterministic):

* `stgMeanR_zero_add_const`: at clock `0`, raising the word's harmonic function and the offset by the same constant
  does not change the stage-start mean;
* **`integral_stgMeanR_zero_conv`**: if the prefix version `R'` agrees with the current version `R` up to the stage
  start `a₀`, and on `ℍ` the current typed function is the word's mean raised by `k` with the offset raised by `k`, the
  pairings of a test function supported in the stage chart's domain against the two stage-start means agree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist.StagedLaw GW2Rd

/-- **At clock `0`, raising the harmonic function and the offset by the same constant keeps the stage mean**, on the
stage chart's domain. -/
theorem stgMeanR_zero_add_const (κ : ℝ) (rec : RecData) {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    (a₀ : ℝ≥0) {U U' u₀ : ℂ → ℝ} {σ k : ℝ} (hU : ∀ z ∈ H, U z = U' z + k) {y : ℂ}
    (hy : y ∈ ((stgChart (Supp8.RelSafeS.relChart rec) R a₀).dom : Set ℂ)) :
    stgMeanR κ rec R a₀ 0 U u₀ (σ + k) y = stgMeanR κ rec R a₀ 0 U' u₀ σ y := by
  have hconf := isConformal_stgChart (Supp8.RelSafeS.isConformal_relChart rec) hR hR0 a₀
  have hH := hconf.fwd_mem hy
  have h0 : (stgChart (Supp8.RelSafeS.relChart rec) R a₀).1 y ≠ 0 := fun h0 => by
    rw [h0] at hH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)
  have hw : Ito.rpath (stgDrv R a₀) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
  unfold stgMeanR
  rw [Coupling.MartMeans2.couplingMean_zero κ hw U h0, Coupling.MartMeans2.couplingMean_zero κ hw U' h0, hU _ hH]
  ring

/-- **The prefix version's stage-start pairing is the current instance's.** -/
theorem integral_stgMeanR_zero_conv (κ : ℝ) (rec : RecData) {R R' : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    (hR' : Continuous R') {a₀ : ℝ≥0} (hRR : ∀ u ≤ a₀, R' u = R u) {U Uw u₀ : ℂ → ℝ} {σ k : ℝ}
    (hU : ∀ z ∈ H, U z = Uw z + k) (φ : LQGMetric.TestOn upperHalfPlaneOpens)
    (hφ : tsupport φ ⊆ ((stgChart (Supp8.RelSafeS.relChart rec) R a₀).dom : Set ℂ)) :
    ∫ z, stgMeanR κ rec R' a₀ 0 Uw u₀ σ z * φ z = ∫ z, stgMeanR κ rec R a₀ 0 U u₀ (σ + k) z * φ z := by
  congr 1
  funext z
  by_cases hz : z ∈ tsupport φ
  · have hz' := hφ hz
    rw [stgMeanR_zero_add_const κ rec hR hR0 a₀ hU hz',
      stgMeanR_zero_congr κ rec hR hR0 hR' (fun u hu => (hRR u hu).symm) Uw u₀ σ hz']
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

end InteractingSLE.Theorem14.GW2Psm
