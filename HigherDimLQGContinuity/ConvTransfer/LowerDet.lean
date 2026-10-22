import HigherDimLQGContinuity.ConvTransfer.Median
import HigherDimLQGContinuity.ConvTransfer.Corr
import HigherDimLQGMetric.DGZ.AdapterNondeg

/-! A finite cubical crossing barrier for pairs on two Euclidean spheres. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (cbox obox)
open HigherDimLQGMetric.DGZ

/-- The outer point of a scaled sphere pair lies beyond the doubled box that
contains the inner point. The fixed radius works for all `r ∈ (1/2,1]`. -/
theorem convCross_outer_not_obox {d : ℕ} {c v x y : Rd d}
    {a c' r ρ : ℝ} (hr : 1 / 2 < r) (hr1 : r ≤ 1)
    (hρ : ρ = (c' - a) / (8 * (Real.sqrt d + 1)))
    (ha : a < c') (hx : x ∈ sphere c a) (hy : y ∈ sphere c c')
    (hcover : r⁻¹ • x ∈ obox v ρ) :
    r⁻¹ • y ∉ obox v (2 * ρ) := by
  have hr0 : 0 < r := by linarith
  have hden : 0 < 8 * (Real.sqrt d + 1) := by positivity
  have hρ0 : 0 < ρ := by rw [hρ]; exact div_pos (by linarith) hden
  have hdiff : c' - a ≤ ‖r⁻¹ • x - r⁻¹ • y‖ := by
    have hxy : c' - a ≤ ‖x - y‖ := by
      have hyc : dist y c = c' := hy
      have hxc : dist x c = a := hx
      have hh := dist_triangle y x c
      rw [hyc, hxc, dist_comm y x, dist_eq_norm] at hh
      linarith
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
    have hri : 1 ≤ r⁻¹ := by simpa only [one_div] using (one_le_div hr0).2 hr1
    nlinarith [mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 hri), norm_nonneg (x-y)]
  intro hout
  have hnear₁ : ‖r⁻¹ • x - v‖ ≤ Real.sqrt d * ρ := by
    simpa only [norm_sub_rev] using (tn_norm_sub_le hcover)
  have hnear₂ : ‖v - r⁻¹ • y‖ ≤ Real.sqrt d * (2 * ρ) := tn_norm_sub_le hout
  have htri : ‖r⁻¹ • x - r⁻¹ • y‖ ≤
      ‖r⁻¹ • x - v‖ + ‖v - r⁻¹ • y‖ := by
    calc
      _ = ‖(r⁻¹ • x - v) + (v - r⁻¹ • y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hbound : Real.sqrt d * ρ + Real.sqrt d * (2 * ρ) < c' - a := by
    have hA : 3 * Real.sqrt d < 8 * (Real.sqrt d + 1) := by
      have := Real.sqrt_nonneg (d : ℝ)
      nlinarith
    have hmul := mul_lt_mul_of_pos_right hA (by linarith : 0 < c' - a)
    have ht : 3 * Real.sqrt d * ρ < c' - a := by
      rw [hρ]
      have heq : 3 * Real.sqrt d * ((c' - a) / (8 * (Real.sqrt d + 1))) =
          (3 * Real.sqrt d * (c' - a)) / (8 * (Real.sqrt d + 1)) := by ring
      rw [heq]
      exact (div_lt_iff₀ hden).2 (by nlinarith [hmul])
    nlinarith
  linarith

/-- The crossing of one finite cubical shell is bounded by the distance of
every scaled sphere pair, after a bounded field perturbation on that shell. -/
theorem convCross_box_le_pair {d : ℕ} {ξ r a c' ρ Γ : ℝ}
    {c v x y : Rd d} {φ ψ : Rd d → ℝ}
    (hξ : 0 ≤ ξ) (hr : 1 / 2 < r) (hr1 : r ≤ 1)
    (ha : a < c')
    (hρ : ρ = (c' - a) / (8 * (Real.sqrt d + 1)))
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hx : x ∈ sphere c a) (hy : y ∈ sphere c c')
    (hcover : r⁻¹ • x ∈ obox v ρ)
    (hDiff : ∀ z ∈ cbox v (2 * ρ) \ obox v ρ,
      |ψ z - φ (r • z)| ≤ Γ) :
    acrossDist ξ ψ v (2 * ρ) ρ ≤
      Real.exp (ξ * Γ) * lfppMetric ξ (fun z => φ (r • z))
        (r⁻¹ • x) (r⁻¹ • y) := by
  have hρ0 : 0 < ρ := by
    rw [hρ]
    exact div_pos (by linarith) (by positivity)
  have hp : r⁻¹ • x ∈ cbox v ρ := HigherDimLFPP.DGZ.obox_subset_cbox _ _ hcover
  have hq : r⁻¹ • y ∉ obox v (2 * ρ) :=
    convCross_outer_not_obox hr hr1 hρ ha hx hy hcover
  have hφc : Continuous (fun z => φ (r • z)) :=
    hφ.comp (continuous_id.const_smul r)
  have hcomp : acrossDist ξ ψ v (2 * ρ) ρ ≤
      Real.exp (ξ * Γ) * acrossDist ξ (fun z => φ (r • z)) v (2 * ρ) ρ := by
    have hh := acrossDist_le_exp_mul (ξ := ξ) (c := v) (r₁ := 2 * ρ)
      (r₂ := ρ) hψ hφc (by linarith) hDiff
    rwa [abs_of_nonneg hξ] at hh
  exact hcomp.trans (mul_le_mul_of_nonneg_left
    (acrossDist_le_lfppMetric_of_mem hφc (by linarith) hp hq)
    (Real.exp_pos _).le)

end HigherDimLQGContinuity
