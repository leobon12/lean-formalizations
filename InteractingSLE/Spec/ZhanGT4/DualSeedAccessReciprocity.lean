/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessAxis
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessDeriv

/-!
# Reciprocity at fixed seed accesses

Packet PROVE-ZHAN-GT4-A22. The algebraic two-view identity uses common
chart-access values and derivatives. It does not differentiate the first
physical map at its seed. The map identities are explicit premises here;
`DualSeedAccessTransport` supplies the seed-access ones from clearance.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace InteractingSLE.ZhanGT4

/-- Two-view logarithmic reciprocity with integrated first-curve seed
coordinates. The correction involves only the first coordinate's reference
partition function and the ordinary derivative at the other source.
This statement uses the raw positive-time logarithm, not its entrance value. -/
theorem seed_access_log_reciprocity {n : ℕ} (d : SeedData n) (e : FrzData n)
    {s t w G : ℝ} (hκ : d.κ ≠ 0) (heκ : e.κ = 16 / d.κ)
    (her : e.r = fun m => -(d.κ / 4) * d.r m)
    (hF0 : e.F 0 t w = d.A20 s) (hF1 : e.F 1 t w = d.A21 s * G)
    (h20 : e.A20 t = d.A 0 s) (h21 : e.A21 t = d.A 1 s)
    (hB0 : ∀ m, e.B0 t m = d.B0 s m) (hB1 : ∀ m, e.B1 t m = d.B1 s m)
    (hL : frzLogF e.W e.W' e.a e.φ t = d.L s)
    (hd21 : d.A21 s ≠ 0) (hG : G ≠ 0) :
    e.ell t w = d.ell s (d.W s) + (d.LT0 s + d.LS0 s (d.W s)) +
      dualAlpha (16 / d.κ) * Real.log G := by
  have hα : (3 * (16 / d.κ) - 8) / 16 = dualAlpha d.κ := by
    unfold dualAlpha
    field_simp
    ring
  have hr (m : Fin n) : -(16 / d.κ / 4) * (-(d.κ / 4) * d.r m) = d.r m := by
    field_simp
    ring
  have hneg : Real.log (d.A20 s - d.A 0 s) = Real.log (d.A 0 s - d.A20 s) := by
    rw [← Real.log_neg_eq_log (d.A 0 s - d.A20 s), neg_sub]
  simp only [FrzData.ell, FrzData.LT, FrzData.LS, SeedData.ell, SeedData.LT, SeedData.LS,
    dualLogTime, dualLogSpace, d.F_driver, heκ, her, hF0, hF1, h20, h21, hB0, hB1, hL,
    dualAlpha_dual hκ, dualLambda_dual hκ, dualGamma_dual hκ, dualDelta_dual hκ,
    hα, hr, Real.log_mul hd21 hG, hneg, Finset.sum_add_distrib]
  ring

/-- After subtracting the fused original-source reference, the opposite
field is the seeded logarithm plus the displayed normalization correction.
The remaining global task is to identify this correction at the entrance
and paste the finite staircase pieces. -/
theorem seed_access_fused_reciprocity {n : ℕ} (d : SeedData n) (e : FrzData n)
    {s t w G p : ℝ} (hκ : d.κ ≠ 0) (heκ : e.κ = 16 / d.κ)
    (her : e.r = fun m => -(d.κ / 4) * d.r m)
    (hF0 : e.F 0 t w = d.A20 s) (hF1 : e.F 1 t w = d.A21 s * G)
    (h20 : e.A20 t = d.A 0 s) (h21 : e.A21 t = d.A 1 s)
    (hB0 : ∀ m, e.B0 t m = d.B0 s m) (hB1 : ∀ m, e.B1 t m = d.B1 s m)
    (hL : frzLogF e.W e.W' e.a e.φ t = d.L s)
    (hd21 : d.A21 s ≠ 0) (hG : G ≠ 0) :
    e.seedAccessEll p t w = d.ell s (d.W s) + (d.LT0 s + d.LS0 s (d.W s)) +
      dualAlpha (16 / d.κ) * Real.log G -
      dualGamma e.κ e.seedAccessExponent * Real.log (deriv (QuantumZipper.fwdMap e.W t) p).re -
      e.seedAccessExponent * Real.log (w - e.seedAccessSource p t) := by
  rw [FrzData.seedAccessEll,
    seed_access_log_reciprocity d e hκ heκ her hF0 hF1 h20 h21 hB0 hB1 hL hd21 hG]

end InteractingSLE.ZhanGT4
