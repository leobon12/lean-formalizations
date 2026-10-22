import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Sharp.GridCount

/-!
# Polynomial count of site centres at one radius

The catalogue centre set is a subset of a finite integer box. This bounds
its size by a fixed multiple of the inverse squared site scale to the
dimension, as needed in the Proposition 4.5 depth condition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The radius-`r` site grid inside the radius-four ball contains at most
`((160√d+5)/Δ²)^d` points when `Δ² ≤ r` and `Δ ≤ 1`. -/
theorem q11_site_grid_card {d : ℕ} (hd : 1 ≤ d)
    {Δ r : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hr : Δ ^ (2 : ℕ) ≤ r) (Z : Finset (Rd d))
    (hZ : ∀ z ∈ Z,
      z ∈ HigherDimLQGMetric.gridPts (r / (20 * Real.sqrt d)) ∧
        z ∈ ball (0 : Rd d) 4) :
    ((Z.card : ℝ) ≤ ((160 * Real.sqrt d + 5) / Δ ^ (2 : ℕ)) ^ d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hr0 : 0 < r := lt_of_lt_of_le (pow_pos hΔ _) hr
  let step : ℝ := r / (20 * Real.sqrt d)
  have hstep : 0 < step := by dsimp [step]; positivity
  let N : ℕ := ⌈4 / step⌉₊ + 1
  have hsubset : Z ⊆ shellGridBox d N step := by
    intro z hz
    have h := hZ z hz
    exact grid_ball_subset_shellGridBox (d := d) hstep (by norm_num)
      (show z ∈ gridPts step ∩ ball (0 : Rd d) 4 from h)
  have hcard : ((Z.card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ d) := by
    have h₁ := Finset.card_le_card hsubset
    have h₂ := card_shellGridBox_le d N step
    exact_mod_cast h₁.trans h₂
  have hN : (N : ℝ) < 4 / step + 2 := by
    dsimp [N]
    push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 / step)]
  have hq : 8 / step = 160 * Real.sqrt d / r := by
    dsimp [step]
    field_simp
    ring
  have hq2 : 2 * (4 / step) = 160 * Real.sqrt d / r := by
    calc 2 * (4 / step) = 8 / step := by ring
      _ = 160 * Real.sqrt d / r := hq
  have hΔ2 : 0 < Δ ^ (2 : ℕ) := pow_pos hΔ _
  have hrec : r⁻¹ ≤ (Δ ^ (2 : ℕ))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hΔ2 hr
  have hrec1 : 1 ≤ (Δ ^ (2 : ℕ))⁻¹ :=
    (one_le_inv_iff₀).mpr ⟨hΔ2, pow_le_one₀ hΔ.le hΔ1⟩
  have hbase : 2 * (N : ℝ) + 1 ≤ (160 * Real.sqrt d + 5) / Δ ^ (2 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hrec
      (by positivity : 0 ≤ 160 * Real.sqrt d)
    have hmul' : 160 * Real.sqrt d / r ≤
        160 * Real.sqrt d / Δ ^ (2 : ℕ) := by
      simpa only [div_eq_mul_inv] using hmul
    have hfive : (5 : ℝ) ≤ 5 / Δ ^ (2 : ℕ) := by
      have h := mul_le_mul_of_nonneg_left hrec1 (by norm_num : (0 : ℝ) ≤ 5)
      simpa only [div_eq_mul_inv, mul_one] using h
    rw [add_div]
    linarith only [hN, hq2, hmul', hfive]
  exact hcard.trans (pow_le_pow_left₀ (by positivity) hbase d)

end HigherDimLQGContinuity
