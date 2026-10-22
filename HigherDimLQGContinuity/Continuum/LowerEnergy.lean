import HigherDimLQGContinuity.Continuum.LowerGrid

/-! The countable dyadic sum controlling all shell crossings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

def l2_lowerEnergy {d : ℕ} (D : DistRd d → ContMetric d)
    (R β q : ℝ) (g : DistRd d) : ℝ≥0∞ :=
  1 + ∑' k : ℕ, l2_lowerGridSum D R β q k g

theorem l2_measurable_lowerEnergy {d : ℕ} {D : DistRd d → ContMetric d}
    (hD : Measurable D) (R β q : ℝ) :
    Measurable (l2_lowerEnergy D R β q) := by
  unfold l2_lowerEnergy
  exact measurable_const.add (Measurable.tsum fun k =>
    l2_measurable_lowerGridSum hD R β q k)

theorem l2_lowerRadius_tsum :
    (∑' k : ℕ, ENNReal.ofReal (l2_lowerRadius k)) = 1 / 4 := by
  have hr (k : ℕ) : ENNReal.ofReal (l2_lowerRadius k) =
      (2⁻¹ : ℝ≥0∞) ^ (k + 3) := by
    dsimp [l2_lowerRadius]
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num [ENNReal.ofReal_div_of_pos]
  simp_rw [hr, pow_add]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
  calc
    (2 : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 3 =
        (2 * 2⁻¹) * (2⁻¹) ^ 2 := by ring
    _ = (2⁻¹ : ℝ≥0∞) ^ 2 := by
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ = (4 : ℝ≥0∞)⁻¹ := by rw [← ENNReal.inv_pow]; norm_num
    _ = 1 / 4 := by norm_num

/-- The energy of all dyadic grids has one uniform first moment. -/
theorem continuum_lowerEnergy_moment {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ q β : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hq : 0 < q)
    (hβ : 1 ≤ q * (β - 1 - Real.sqrt (2 * d) * b) - q ^ 2 * b ^ 2 - d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ R : ℝ, 1 ≤ R →
          (∫⁻ g, l2_lowerEnergy D R β q g ∂(normLGFLaw d)) ≤
            ENNReal.ofReal (1 + C * (16 * d * (R + 2) + 5) ^ d *
              (R + 3) ^ (2 * q ^ 2 * b ^ 2) / 4) := by
  obtain ⟨C, hC0, hgrid⟩ := continuum_gridMoment hd hκ hC1 hC2
    hb hμ hμ1 hq hβ
  refine ⟨C, hC0, fun ξ hξ D hD R hR => ?_⟩
  let M : ℝ := C * (16 * d * (R + 2) + 5) ^ d *
    (R + 3) ^ (2 * q ^ 2 * b ^ 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  letI := l9b_normLGFLaw_prob (show 2 ≤ d by omega)
  have hsum : (∫⁻ g, (∑' k : ℕ, l2_lowerGridSum D R β q k g)
      ∂(normLGFLaw d)) ≤ ENNReal.ofReal (M / 4) := by
    calc
      (∫⁻ g, (∑' k : ℕ, l2_lowerGridSum D R β q k g)
        ∂(normLGFLaw d)) =
          ∑' k : ℕ, ∫⁻ g, l2_lowerGridSum D R β q k g ∂(normLGFLaw d) := by
        exact lintegral_tsum fun k =>
          (l2_measurable_lowerGridSum hD.measurable R β q k).aemeasurable
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (M * l2_lowerRadius k) := by
        apply ENNReal.tsum_le_tsum
        intro k
        simpa only [M] using hgrid ξ hξ D hD R hR k
      _ = ENNReal.ofReal M *
          (∑' k : ℕ, ENNReal.ofReal (l2_lowerRadius k)) := by
        simp_rw [ENNReal.ofReal_mul hM]
        exact ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (M / 4) := by
        rw [l2_lowerRadius_tsum,
          show (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) by
            norm_num [ENNReal.ofReal_div_of_pos],
          ← ENNReal.ofReal_mul hM]
        congr 1
        ring
  calc
    (∫⁻ g, l2_lowerEnergy D R β q g ∂(normLGFLaw d)) =
        1 + ∫⁻ g, (∑' k : ℕ, l2_lowerGridSum D R β q k g)
          ∂(normLGFLaw d) := by
      unfold l2_lowerEnergy
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ 1 + ENNReal.ofReal (M / 4) := add_le_add_right hsum _
    _ = ENNReal.ofReal (1 + M / 4) := by
      rw [← ENNReal.ofReal_one]
      rw [← ENNReal.ofReal_add (by norm_num) (div_nonneg hM (by norm_num))]
    _ = ENNReal.ofReal (1 + C * (16 * d * (R + 2) + 5) ^ d *
      (R + 3) ^ (2 * q ^ 2 * b ^ 2) / 4) := by rfl

end HigherDimLQGContinuity
