/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessSlope

/-!
# Seed-access transport in a protected two-curve rectangle

Packet PROVE-ZHAN-GT4-A22. With the first curve frozen, every protected
integrated coordinate and all its map derivatives are read in the opposite
image flow. The divided-difference identity also includes equal accesses.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)

namespace OwnData

variable {W₁ W₂ b U : ℝ → ℝ} {as Ws : ℝ → ℝ → ℝ} {S s T ρ : ℝ}
    (h₁ : ∀ t ∈ Icc (0 : ℝ) T,
      OwnData W₁ (fwdHull W₂ t) (frzChart W₂ t) S (as t) (Ws t))
    (hs : s ∈ Icc (0 : ℝ) S)
    (h₂ : OwnData W₂ (fwdHull W₁ s) (frzChart W₁ s) T b U)
    (hρ : 0 < ρ)
include h₁ hs h₂ hρ

/-- Actual boundary-coordinate transport on the whole opposite time interval.
The access is specified in the frozen first chart, so a seed is permitted. -/
theorem exists_transposed_access_flow {v : ℝ}
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball (v : ℂ) ρ)
      ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t)) :
    ∃ q : ℝ → ℂ, IsForwardSol U (v : ℂ) (b T) q ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ k : ℕ,
        deriv^[k] (ownExt W₁ (Ws t) (as t) (frzChart W₂ t) s) v =
          deriv^[k] (fun z => fwdMap U (b t) z + U (b t)) v := by
  obtain ⟨q, hq⟩ := exists_transposed_sol_of_clear h₂.toImgData hρ
    (hclear T ⟨h₂.pos.le, le_rfl⟩)
  exact ⟨q, hq, fun t ht k => (h₁ t ht).iterate_deriv_ownExt_eq_transposed_at_clear
    hs h₂.toImgData ht hρ (hclear t ht) hq k⟩

/-- The normalized distance numerator in the first view is the divided
 difference of the opposite image chain, including the derivative on the diagonal. -/
theorem dslope_ownExt_eq_transposed {u v : ℝ}
    (hclearu : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball (u : ℂ) ρ)
      ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t))
    (hclearv : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball (v : ℂ) ρ)
      ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    dslope (fun x : ℝ => (ownExt W₁ (Ws t) (as t) (frzChart W₂ t) s x).re) u v =
      dslope (fun x => frzImg U b x t) u v := by
  obtain ⟨q, hq, heq⟩ := exists_transposed_access_flow h₁ hs h₂ hρ hclearu
  obtain ⟨r, -, her⟩ := exists_transposed_access_flow h₁ hs h₂ hρ hclearv
  rcases eq_or_ne v u with rfl | hne
  · rw [dslope_same, dslope_same, (hasDerivAt_frzImg_real h₂.contW' hq (h₂.mapsTo_clock ht)).deriv]
    have hd := ((h₁ t ht).ownExt_props hs (hclearu t ht)).1
    have hdv := hd.differentiableAt (ball_mem_nhds (v : ℂ) (by positivity : 0 < ρ / 2))
    rw [hdv.hasDerivAt.real_of_complex.deriv]
    have he := congrArg Complex.re (heq t ht 1)
    simpa only [Function.iterate_one, deriv_add_const, frzImgD] using he
  · rw [dslope_of_ne _ hne, dslope_of_ne _ hne, slope_def_field, slope_def_field]
    have hu := congrArg Complex.re (heq t ht 0)
    have hv := congrArg Complex.re (her t ht 0)
    simp only [Function.iterate_zero, id_eq, Complex.add_re, Complex.ofReal_re] at hu hv
    change (_ - _) / (v - u) = (frzImg U b v t - frzImg U b u t) / (v - u)
    rw [hu, hv]
    rfl

/-- The value and first derivative of a protected seed access obey the
opposite flow, with no derivative of the physical first hull map. -/
theorem seed_access_value_deriv {v : ℝ}
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball (v : ℂ) ρ)
      ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      (ownExt W₁ (Ws t) (as t) (frzChart W₂ t) s v).re = frzImg U b v t ∧
      (deriv (ownExt W₁ (Ws t) (as t) (frzChart W₂ t) s) v).re = frzImgD U b v t := by
  obtain ⟨q, -, he⟩ := exists_transposed_access_flow h₁ hs h₂ hρ hclear
  intro t ht
  constructor
  · have hh := congrArg Complex.re (he t ht 0)
    simpa only [Function.iterate_zero, id_eq, frzImg, Complex.add_re, Complex.ofReal_re] using hh
  · have hh := congrArg Complex.re (he t ht 1)
    simpa only [Function.iterate_one, deriv_add_const, frzImgD] using hh

end OwnData
end InteractingSLE.ZhanGT4
