import HigherDimLQGContinuity.MomentsW2.Direct
import LQGMetric.Papers.DFGPS.P3_10Moment

/-!
# Dyadic lower tails give inverse moments

This is the analytic layer-cake step of W2. It reuses the certified general
tail-to-moment theorem of DFGPS after interpolating a geometric sequence of tails.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

/-- A geometric lower tail implies any inverse moment below its decay exponent. -/
theorem w2_inv_moment_of_geom_tail {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ≥0∞)
    {c r C a q : ℝ} (hc : 0 < c) (hr : 1 < r) (hC : 0 ≤ C)
    (hq : 0 < q) (hqa : q < a)
    (htail : ∀ m : ℕ,
      P {ω | Y ω < ENNReal.ofReal (c * r ^ (-(m : ℝ)))} ≤
        ENNReal.ofReal (C * r ^ (-(a * m)))) :
    ∫⁻ ω, (Y ω)⁻¹ ^ q ∂P ≤
      ENNReal.ofReal (LQGMetric.DFGPS.momBd q a (C * r ^ a * c ^ (-a)) (max 1 c⁻¹)) := by
  let t₀ : ℝ := max 1 c⁻¹
  have ht₀ : 1 ≤ t₀ := le_max_left _ _
  have hct₀ : c⁻¹ ≤ t₀ := le_max_right _ _
  let C' : ℝ := C * r ^ a * c ^ (-a)
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hT : ∀ t : ℝ, t₀ ≤ t →
      P {ω | Y ω < ENNReal.ofReal t⁻¹} ≤ ENNReal.ofReal (C' * t ^ (-a)) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) (ht₀.trans ht)
    have hct : 1 ≤ c * t := by
      have ht' : c⁻¹ ≤ t := hct₀.trans ht
      have hm := mul_le_mul_of_nonneg_left ht' hc.le
      rw [mul_inv_cancel₀ hc.ne'] at hm
      exact hm
    obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near hct hr
    have hm1' : r ^ (m : ℝ) ≤ c * t := by simpa only [Real.rpow_natCast] using hm1
    have hm2' : c * t < r ^ ((m + 1 : ℕ) : ℝ) := by
      simpa only [Real.rpow_natCast] using hm2
    have hthresh : t⁻¹ ≤ c * r ^ (-(m : ℝ)) := by
      have hp : 0 < r ^ (m : ℝ) := Real.rpow_pos_of_pos (by linarith) _
      have he : r ^ (-(m : ℝ)) = (r ^ (m : ℝ))⁻¹ := by
        rw [Real.rpow_neg (by linarith : 0 ≤ r)]
      rw [he]
      have hfrac : 1 / t ≤ c / r ^ (m : ℝ) := by
        apply (le_div_iff₀ hp).2
        rw [one_div_mul_eq_div]
        exact (div_le_iff₀ htpos).2 hm1'
      simpa only [one_div, div_eq_mul_inv, one_mul] using hfrac
    have hP : P {ω | Y ω < ENNReal.ofReal t⁻¹} ≤
        ENNReal.ofReal (C * r ^ (-(a * m))) := by
      exact (measure_mono fun ω hω => lt_of_lt_of_le hω
        (ENNReal.ofReal_le_ofReal hthresh)).trans (htail m)
    have hrpos : 0 < r := by linarith
    have hmp : 0 < r ^ (m : ℝ) := Real.rpow_pos_of_pos hrpos _
    have hx : 0 < c * t := mul_pos hc htpos
    have hdiv : c * t / r < r ^ (m : ℝ) := by
      apply (div_lt_iff₀ hrpos).2
      have he : r ^ ((m + 1 : ℕ) : ℝ) = r ^ (m : ℝ) * r := by
        rw [Nat.cast_add, Nat.cast_one, Real.rpow_add hrpos]
        simp
      rw [he] at hm2'
      nlinarith only [hm2']
    have hpow : (r ^ (m : ℝ)) ^ (-a) ≤ (c * t / r) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hx hrpos) hdiv.le (by linarith)
    have he1 : (r ^ (m : ℝ)) ^ (-a) = r ^ (-(a * m)) := by
      rw [← Real.rpow_mul hrpos.le]
      ring_nf
    have he2 : (c * t / r) ^ (-a) = r ^ a * c ^ (-a) * t ^ (-a) := by
      rw [Real.div_rpow (mul_nonneg hc.le htpos.le) hrpos.le,
        Real.mul_rpow hc.le htpos.le, Real.rpow_neg hrpos.le, div_inv_eq_mul]
      ring
    have hbound : C * r ^ (-(a * m)) ≤ C' * t ^ (-a) := by
      calc
        C * r ^ (-(a * m)) = C * (r ^ (m : ℝ)) ^ (-a) := by rw [he1]
        _ ≤ C * (c * t / r) ^ (-a) := mul_le_mul_of_nonneg_left hpow hC
        _ = C' * t ^ (-a) := by rw [he2]; dsimp [C']; ring
    exact hP.trans (ENNReal.ofReal_le_ofReal hbound)
  simpa only [ENNReal.inv_rpow, ENNReal.rpow_neg, neg_neg] using
    (LQGMetric.DFGPS.lintegral_rpow_neg_le_of_tail P Y (p := -q) (a := a)
      (C := C') (t₀ := t₀) (by linarith) (by linarith) hC' ht₀ hT)

end HigherDimLQGContinuity
