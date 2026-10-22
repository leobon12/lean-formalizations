import HigherDimLQGContinuity.MomentsW2.Coarse
import HigherDimLQGMetric.DGZ.TightBasics
import HigherDimLQGMetric.DGZ.CompareCor52

/-!
# CRUDE comparison of dyadic normalizers for W2

The ratio `a_n(1/2)/a_{n-m}(3/4)` is controlled without the lower half of
Appendix A's (A.2), following ruling N8.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ}

/-- At the empty dyadic band, the unit-distance quantile is at most the Euclidean value. -/
theorem w2_aQ_zero_le_one (hd : 2 ≤ d) (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : DGZ.IsDyadicRealization κ P W H) (ξ : ℝ) :
    DGZ.aQ P H ξ 0 (3 / 4 : ℝ≥0∞) ≤ 1 := by
  have hzero := DGZ.ae_forall_eq_zero_of_isBandVersion_self hκ hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  have hprob : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  have hdist : ∀ᵐ ω ∂P, HigherDimLFPP.lfppDistance d ξ (fun z => H 0 z ω) ≤ 1 := by
    filter_upwards [hzero] with ω hω
    have hbound : ∀ z ∈ HigherDimLFPP.cube d, |H 0 z ω| ≤ (0 : ℝ) := by
      intro z _
      rw [hω z, abs_zero]
    have hup := HigherDimLFPP.lfppDistance_le_exp (ζ := ξ) (by omega : 0 < d)
      ((hH.band 0).continuous ω) hbound
    simpa only [mul_zero, Real.exp_zero] using hup
  have hm : MeasurableSet {ω | HigherDimLFPP.lfppDistance d ξ (fun z => H 0 z ω) ≤ 1} :=
    measurableSet_le ((hH.band 0).measurable_lfppDistance ξ) measurable_const
  have hcomp : P {ω | ¬ HigherDimLFPP.lfppDistance d ξ (fun z => H 0 z ω) ≤ 1} = 0 :=
    ae_iff.1 hdist
  have hfull : P {ω | HigherDimLFPP.lfppDistance d ξ (fun z => H 0 z ω) ≤ 1} = 1 := by
    have hsum := measure_add_measure_compl (μ := P) hm
    rw [show ({ω | HigherDimLFPP.lfppDistance d ξ (fun z => H 0 z ω) ≤ 1} : Set Ω)ᶜ =
      {ω | ¬ HigherDimLFPP.lfppDistance d ξ (fun z => H 0 z ω) ≤ 1} from rfl,
      hcomp, add_zero, @IsProbabilityMeasure.measure_univ _ _ P hprob] at hsum
    exact hsum
  apply (DGZ.cmp_le_prob_iff_aQ_le hH ξ 0 (by norm_num) (by
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num) 1).1
  rw [hfull]
  exact le_of_lt (by
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num : (3 / 4 : ℝ≥0∞) < 1)

/-- Uniform CRUDE normalization comparison at quantiles `1/2` and `3/4`. -/
theorem w2_normalizer_le (hCr : CrudeLowerShape d κ)
    {b μ ξ : ℝ} (hξ : UHyp d κ b μ ξ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : DGZ.IsDyadicRealization κ P W H) {m n : ℕ} (hmn : m ≤ n) :
    DGZ.aQ P H ξ n 2⁻¹ ≤
      4 * (2 : ℝ) ^ (b ^ 2 * m / 2) * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞) := by
  have hq0 : (0 : ℝ≥0∞) < 2⁻¹ := by norm_num
  have hqq : (2⁻¹ : ℝ≥0∞) < 3 / 4 := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    have he : (2⁻¹ : ℝ≥0∞) * 4 = 2 := by
      calc
        (2⁻¹ : ℝ≥0∞) * 4 = 2⁻¹ * (2 * 2) := by norm_num
        _ = 2 := by rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]; norm_num
    rw [he]
    norm_num
  have hq1 : (3 / 4 : ℝ≥0∞) < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hcr := hCr ξ hξ.base.xi_pos.le 2⁻¹ (3 / 4 : ℝ≥0∞)
    hq0 hqq hq1 Ω P W H hH n m hmn
  have hdiff : ((3 / 4 : ℝ≥0∞) - 2⁻¹).toReal⁻¹ = (4 : ℝ) := by
    rw [ENNReal.toReal_sub_of_le hqq.le (ne_top_of_lt hq1), ENNReal.toReal_div,
      ENNReal.toReal_inv]
    norm_num
  rw [hdiff] at hcr
  have hsq : ξ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hξ.base.xi_pos.le hξ.le_b 2
  have hexp : (2 : ℝ) ^ (ξ ^ 2 * m / 2) ≤ (2 : ℝ) ^ (b ^ 2 * m / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by gcongr)
  have hd0 : 0 < d := by have := hξ.base.dim; omega
  have hqpos : 0 ≤ DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞) :=
    (DGZ.tight_aQ_pos hd0 hH ξ (n - m) (by norm_num) hq1).le
  calc
    DGZ.aQ P H ξ n 2⁻¹ ≤
        4 * (2 : ℝ) ^ (ξ ^ 2 * m / 2) * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞) := hcr
    _ ≤ _ := by gcongr

/-- CRUDE at `m = n` gives a direct deterministic upper bound on the median. -/
theorem w2_normalizer_direct (hκ : IsLFPPKernel κ) (hCr : CrudeLowerShape d κ)
    {b μ ξ : ℝ} (hξ : UHyp d κ b μ ξ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : DGZ.IsDyadicRealization κ P W H) (n : ℕ) :
    DGZ.aQ P H ξ n 2⁻¹ ≤ 4 * (2 : ℝ) ^ (b ^ 2 * n / 2) := by
  have h := w2_normalizer_le hCr hξ hH (le_refl n)
  simp only [Nat.sub_self] at h
  have hz := w2_aQ_zero_le_one hξ.base.dim hκ hH ξ
  have hmul : 0 ≤ 4 * (2 : ℝ) ^ (b ^ 2 * n / 2) := by positivity
  simpa only [mul_one] using h.trans (mul_le_mul_of_nonneg_left hz hmul)

end HigherDimLQGContinuity
