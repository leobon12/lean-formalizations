/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessField
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Axis

/-!
# The fused normalization of the actual seed time axis

Packet PROVE-ZHAN-GT4-A22. The original source derivative and gap occur
with exactly the amalgamated opposite charge, even though the own seeds
coincide. This is an identity for the normalized divided-difference formula.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap logDerivFwd)

/-- The conformal weight of the mirror's amalgamated source, expressed
in the first view's exponents. -/
theorem dualGamma_mirror_seed_fusion {n : ℕ} {κ : ℝ} (hκ : κ ≠ 0) (r : Fin n → ℝ) :
    dualGamma (16 / κ) (-1 / 2 + ∑ m, -(κ / 4) * r m) = dualAlpha κ +
      (∑ m, (dualGamma κ (r m) + r m)) + pairSum (fun m k => dualDelta κ (r m) (r k)) := by
  have he := dualGamma_seed_fusion (16 / κ) (fun m => -(κ / 4) * r m)
  have hα : (3 * (16 / κ) - 8) / 16 = dualAlpha κ := by
    unfold dualAlpha
    field_simp
    ring
  have hr (m : Fin n) : -(16 / κ / 4) * (-(κ / 4) * r m) = r m := by
    field_simp
    ring
  simp only [dualGamma_dual hκ, dualDelta_dual hκ, hr, hα] at he
  exact he

namespace SeedData
variable {n : ℕ} (d : SeedData n)

/-- On an axis with coincident own seeds, the normalized logarithm has
precisely the one-source reference partition function's fused exponents. -/
theorem normEll_eq_fused_axis {t : ℝ} (hκ : d.κ ≠ 0)
    (hd : DifferentiableAt ℂ (ownExt d.W d.W' d.a d.φ t) (d.W t))
    (hV : ∀ m, d.V m t = d.W t) (h21 : d.A21 t = 1) (hL : d.L t = 0) :
    d.normEll t =
      dualGamma (16 / d.κ) (-1 / 2 + ∑ m, -(d.κ / 4) * d.r m) * Real.log (d.A 1 t) +
        (-1 / 2 + ∑ m, -(d.κ / 4) * d.r m) *
          Real.log ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t)) := by
  have hB0 (m : Fin n) : d.B0 t m = d.A 0 t := by
    change d.F 0 t (d.V m t) = _
    rw [hV, d.F_driver]
  have hB1 (m : Fin n) : d.B1 t m = d.A 1 t := by
    change d.F 1 t (d.V m t) = _
    rw [hV, d.F_driver]
  have hds : dslope (d.F 0 t) (d.W t) (d.W t) = d.A 1 t := by
    rw [dslope_same, d.deriv_F_zero hd, d.F_driver]
  have hratio : (d.A20 t - d.A 0 t) / (d.V₀ t - d.W t) =
      (d.A 0 t - d.A20 t) / (d.W t - d.V₀ t) := by
    rw [← neg_sub (d.A 0 t) (d.A20 t), ← neg_sub (d.W t) (d.V₀ t), neg_div_neg_eq]
  rw [dualGamma_mirror_seed_fusion hκ]
  simp only [normEll, h21, hL, hB0, hB1, hV, hds, hratio,
    Real.log_one, mul_zero, sub_zero, zero_add]
  rw [pairSum_mul_const]
  simp only [Finset.sum_add_distrib, Finset.sum_mul, add_mul]
  ring

/-- The actual own-time entrance has the fused-axis formula. There is no
noncollision premise at time zero and no limiting unnormalized product. -/
theorem normEll_zero_eq_fused_axis {A : Set ℂ} {T : ℝ}
    (h : OwnData d.W A d.φ T d.a d.W') (hκ : d.κ ≠ 0)
    {q : ℝ → ℂ} (hq : IsForwardSol d.W' d.ζ₀ (d.a T) q)
    (hV : ∀ m, d.V m 0 = d.W 0) (hG : d.G₀ 0 = 1) :
    d.normEll 0 =
      dualGamma (16 / d.κ) (-1 / 2 + ∑ m, -(d.κ / 4) * d.r m) * Real.log (d.A 1 0) +
        (-1 / 2 + ∑ m, -(d.κ / 4) * d.r m) *
          Real.log ((d.A 0 0 - d.A20 0) / (d.W 0 - d.V₀ 0)) := by
  have ht : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, h.pos.le⟩
  obtain ⟨ρ, _, hc⟩ := h.exists_clearance
  have hd := (h.ownExt_props ht (hc 0 ht)).1
  have hdr := hd.differentiableAt (ball_mem_nhds (d.W 0 : ℂ) (by positivity : 0 < ρ / 2))
  have hbT : 0 ≤ d.a T := (h.mapsTo_clock ⟨h.pos.le, le_rfl⟩).1
  obtain ⟨δ, hδ, hl, hv⟩ := exists_aliveDisc_self hq hbT
  have hder := deriv_fwdMap_aliveDisc h.contW' hq hδ hl hv ⟨(le_rfl : (0 : ℝ) ≤ 0), hbT⟩
  have h21 : d.A21 0 = 1 := by
    simp only [A21, frzImgD, h.a0, hG, hder, logDerivFwd, intervalIntegral.integral_same,
      neg_zero, Complex.exp_zero, Complex.one_re, div_one]
  have hL : d.L 0 = 0 := by simp only [L, frzLogF, intervalIntegral.integral_same]
  exact d.normEll_eq_fused_axis hκ hdr hV h21 hL

end SeedData
end InteractingSLE.ZhanGT4
