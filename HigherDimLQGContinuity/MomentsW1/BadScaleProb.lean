import HigherDimLQGContinuity.MomentsW1.BadScaleFree
import HigherDimLQGMetric.DGZ.AcrossAroundTools

/-! # Fine-field site probability estimates -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (closedSite)
open HigherDimLQGMetric.DGZ

/-- Each bad site, in any finite region, has the quantile probability bound. -/
theorem wnClosed_prob {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (ξ R : ℝ) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq1 : q < 1) {k n : ℕ} (hkn : k ≤ n) (x : Zd d) :
    P (wnClosed P H ξ R q k n x) ≤ 2 * d * (1 - q) := by
  have hG := isBandVersion_sub_of_realization hκ hH hkn
  have hH' : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n / (2 : ℝ)⁻¹ ^ k) 1
      (H (n - k)) :=
    (hH.band (n - k)).congr_band (inv_two_pow_div_inv_two_pow hkn).symm rfl
  have hraw := HigherDimLFPP.DGZ.measure_closedSite_le_lowerQuantile_of_band
    hκ hH.whiteNoise hH.whiteNoise (by positivity) (by positivity) hG hH' ξ
    hq0 hq1 (R + 3) x
  exact (measure_mono (fun _ h => h.2)).trans hraw

/-- A rough coarse site is bounded by one coarse and at most `3^d` fine bad-site events. -/
theorem wnRough_prob {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (ξ R : ℝ) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq1 : q < 1) {k n : ℕ} (hkn : k ≤ n) (y : Zd d) :
    P (wnRough P H ξ R q k n y) ≤ (1 + 3 ^ d) * (2 * d * (1 - q)) := by
  rw [wnRough_eq]
  calc
    P (wnClosed P H ξ R q (k - 1) n y ∪
        ⋃ z ∈ boxF (2 • y) 1, wnClosed P H ξ R q k n z)
        ≤ P (wnClosed P H ξ R q (k - 1) n y) +
          P (⋃ z ∈ boxF (2 • y) 1, wnClosed P H ξ R q k n z) := measure_union_le _ _
    _ ≤ (2 * d * (1 - q)) + ∑ _z ∈ boxF (2 • y) 1, (2 * d * (1 - q)) := by
      apply add_le_add (wnClosed_prob hκ hH ξ R hq0 hq1 (by omega) y)
      exact (measure_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum fun z _ => wnClosed_prob hκ hH ξ R hq0 hq1 hkn z)
    _ = (1 + 3 ^ d) * (2 * d * (1 - q)) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_boxF_ennreal]
      norm_num
      ring

end HigherDimLQGContinuity
