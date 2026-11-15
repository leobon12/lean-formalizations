/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessField

/-!
# Derivatives of the fused opposite-view field

Packet PROVE-ZHAN-GT4-A22. Prove the three space derivatives and the time
derivative of the concrete field, using reflected own-map calculus and the
original separated source's Loewner equation. No physical preimage of a
frozen seed access is required.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)
namespace FrzData
variable {n : ℕ} (d : FrzData n)

/-- Three actual spatial derivatives of the fused density at every
protected point with nonzero source and image gaps. -/
theorem seedAccess_space_derivatives {A : Set ℂ} {T p t x ρ : ℝ}
    (h : OwnData d.W A d.φ T d.a d.W') (ht : t ∈ Icc (0 : ℝ) T)
    (hρ : 0 < ρ)
    (hc : Disjoint (ball (x : ℂ) ρ) ((fun z => fwdMap d.W t z + d.W t) '' A))
    (h1 : d.F 1 t x ≠ 0) (h0 : d.F 0 t x - d.A20 t ≠ 0)
    (hm : ∀ m, d.F 0 t x - d.B0 t m ≠ 0) (hs : x - d.seedAccessSource p t ≠ 0) :
    HasDerivAt (d.seedAccessEll p t) (d.seedAccessX p t x) x ∧
      HasDerivAt (d.seedAccessX p t) (d.seedAccessXX p t x) x ∧
      HasDerivAt (d.seedAccessXX p t) (d.seedAccessXXX p t x) x := by
  have hd := (h.ownExt_props ht hc).1
  have hF (k : ℕ) : HasDerivAt (d.F k t) (d.F (k + 1) t x) x := by
    have hh := (OwnData.differentiableOn_iterDeriv isOpen_ball hd k).differentiableAt
      (ball_mem_nhds (x : ℂ) (by positivity : 0 < ρ / 2))
    change HasDerivAt (fun y : ℝ => (deriv^[k] (ownExt d.W d.W' d.a d.φ t) y).re)
      ((deriv^[k + 1] (ownExt d.W d.W' d.a d.φ t) x).re) x
    simpa only [Function.iterate_succ_apply'] using hh.hasDerivAt.real_of_complex
  have hx := (hasDerivAt_dualLogSpace (κ := d.κ) (r := d.r)
    (hF 0) (hF 1) h1 h0 hm).const_add (d.LT t)
  have hxx := hasDerivAt_dualLogSpaceX (κ := d.κ) (r := d.r)
    (hF 0) (hF 1) (hF 2) h1 h0 hm
  have hxxx := hasDerivAt_dualLogSpaceXX (κ := d.κ) (r := d.r)
    (hF 0) (hF 1) (hF 2) (hF 3) h1 h0 hm
  have hdg := (hasDerivAt_id x).sub_const (d.seedAccessSource p t)
  have hg1 : HasDerivAt (fun y => d.seedAccessExponent * Real.log (y - d.seedAccessSource p t))
      (d.seedAccessExponent / (x - d.seedAccessSource p t)) x := by
    exact ((hdg.log hs).const_mul d.seedAccessExponent).congr_deriv (by simp only [id_eq]; ring)
  have hg2 : HasDerivAt (fun y => d.seedAccessExponent / (y - d.seedAccessSource p t))
      (-d.seedAccessExponent / (x - d.seedAccessSource p t) ^ 2) x := by
    simpa only [zero_mul, mul_one, zero_sub, id_eq] using
      (hasDerivAt_const x d.seedAccessExponent).fun_div hdg hs
  have hg3 : HasDerivAt (fun y => d.seedAccessExponent / (y - d.seedAccessSource p t) ^ 2)
      (-2 * d.seedAccessExponent / (x - d.seedAccessSource p t) ^ 3) x := by
    refine ((hasDerivAt_const x d.seedAccessExponent).fun_div (hdg.pow 2)
      (pow_ne_zero 2 hs)).congr_deriv ?_
    simp only [id_eq, Pi.pow_apply]
    field_simp [hs]
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact (hx.sub_const (dualGamma d.κ d.seedAccessExponent *
      Real.log (deriv (fwdMap d.W t) p).re)).sub hg1
  · change HasDerivAt (fun y => d.LSX t y - d.seedAccessExponent / (y - d.seedAccessSource p t))
      (d.LSXX t x + d.seedAccessExponent / (x - d.seedAccessSource p t) ^ 2) x
    simpa only [FrzData.LSX, FrzData.LSXX, Nat.reduceAdd, neg_div, sub_neg_eq_add]
      using hxx.fun_sub hg2
  · change HasDerivAt (fun y => d.LSXX t y + d.seedAccessExponent / (y - d.seedAccessSource p t) ^ 2)
      (d.LSXXX t x - 2 * d.seedAccessExponent / (x - d.seedAccessSource p t) ^ 3) x
    simpa only [FrzData.LSXX, FrzData.LSXXX, Nat.reduceAdd, neg_mul, neg_div, sub_eq_add_neg]
      using hxxx.fun_add hg3

/-- The actual fixed-space time derivative on a protected box. The
frozen accesses may be seed coordinates, provided they are alive in the image chart. -/
theorem hasDerivWithinAt_seedAccessEll {A : Set ℂ} {T p : ℝ}
    (h : OwnData d.W A d.φ T d.a d.W')
    {q₀ : ℝ → ℂ} (hq₀ : IsForwardSol d.W' d.ζ₀ (d.a T) q₀)
    {q : Fin n → ℝ → ℂ} (hq : ∀ m, IsForwardSol d.W' (d.ζ m) (d.a T) (q m))
    (hζ₀ : ∀ m, d.ζ m ≠ d.ζ₀) (hζ : Function.Injective d.ζ)
    {qS : ℝ → ℂ} (hqS : IsForwardSol d.W (p : ℂ) T qS)
    {a c y r t x : ℝ} (hJ : Icc a c ⊆ Icc 0 T)
    (hc : ∀ u ∈ Icc a c, Disjoint (ball (y : ℂ) (2 * r))
      ((fun z => fwdMap d.W u z + d.W u) '' A))
    (hW : ∀ u ∈ Icc a c, (d.W u : ℂ) ∈ ball (y : ℂ) r)
    (hn : ∀ u ∈ Icc a c, ∀ z ∈ ball (y : ℂ) r,
      dslope (ownExt d.W d.W' d.a d.φ u) (d.W u) z ≠ 0)
    (ht : t ∈ Icc a c) (hx : (x : ℂ) ∈ ball (y : ℂ) r)
    (h1 : d.F 1 t x ≠ 0) (h0 : d.F 0 t x - d.A20 t ≠ 0)
    (hm : ∀ m, d.F 0 t x - d.B0 t m ≠ 0) (hs : x - d.seedAccessSource p t ≠ 0) :
    HasDerivWithinAt (fun u => d.seedAccessEll p u x) (d.seedAccessT p t x) (Icc a c) t := by
  have hLT := (d.hasDerivWithinAt_LT h hq₀ hq hζ₀ hζ (hJ ht)).mono hJ
  have hLS := hasDerivWithinAt_dualLogSpace_time (κ := d.κ) (r := d.r)
    (h.hasDerivWithinAt_re_ownExt_box hJ hc hW hn ht hx)
    (h.hasDerivWithinAt_re_deriv_ownExt_box hJ hc hW hn ht hx)
    ((h.hasDerivWithinAt_frzImg hq₀ (hJ ht)).mono hJ)
    (fun m => (h.hasDerivWithinAt_frzImg (hq m) (hJ ht)).mono hJ) h1 h0 hm
  have hG := ((OwnData.hasDerivWithinAt_log_source_deriv h.cont hqS (hJ ht)).mono hJ).const_mul
    (dualGamma d.κ d.seedAccessExponent)
  have hV := ((source_gmap_rates h.cont hqS (hJ ht)).1).mono hJ
  have hg := ((hV.const_sub x).log hs).const_mul d.seedAccessExponent
  have hd := ((hLT.add hLS).sub hG).sub hg
  refine hd.congr_deriv ?_
  change (d.ellT t x - dualGamma d.κ d.seedAccessExponent * (-2 / (fwdMap d.W t p).re ^ 2) -
    d.seedAccessExponent * (-(2 / (d.seedAccessSource p t - d.W t)) /
      (x - d.seedAccessSource p t))) = d.seedAccessT p t x
  simp only [seedAccessT, seedAccessSource, add_sub_cancel_right]
  ring

end FrzData
end InteractingSLE.ZhanGT4
