/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.DiskFourier
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Polar coordinates on the unit disk and the `L²` coefficient identity (PU4)

Packet PROVE-SEC6-A (specification §6.1, proof of Aux. lemma 29, `source/spec/p145-192.md`,
`#id-PU4`, p. 165): "Parseval's identity and integration with the area element `ρ dρ dt` give
`‖u‖²_{L²(𝔻)} = π ∑ |c_n|²/(|n| + 1)`. Consequently the coefficients `c_n` define a distribution
`T ∈ H^{−1/2}(∂𝔻)`."

## Main results

* `InteractingSLE.Sec6.lintegral_ball_eq_polar`: `∫_𝔻 F = ∫₀¹ ρ ∫_{−π}^{π} F(ρe^{it}) dt dρ` for
  measurable `F ≥ 0`;
* `InteractingSLE.Sec6.summable_sq_diskCoeff_div` (PU4, in the form used): if `u = Re F` is
  square integrable on the disk, then `∑ |c_n|²/(|n| + 1) < ∞`.
-/

noncomputable section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace InteractingSLE.Sec6

theorem polarCoord_symm_eq_polarPt (p : ℝ × ℝ) : Complex.polarCoord.symm p = polarPt p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, polarPt, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

theorem measurable_polarPt : Measurable fun p : ℝ × ℝ => polarPt p.1 p.2 := by
  unfold polarPt; fun_prop

/-- **Polar coordinates on the unit disk.** -/
theorem lintegral_ball_eq_polar {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in ball (0 : ℂ) 1, F z =
      ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal ρ * ∫⁻ t in Ioo (-π) π, F (polarPt ρ t) := by
  have h1 := Complex.lintegral_comp_polarCoord_symm ((ball (0 : ℂ) 1).indicator F)
  rw [lintegral_indicator measurableSet_ball] at h1
  have ht : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  rw [← h1, ht, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 • (ball (0 : ℂ) 1).indicator F (Complex.polarCoord.symm p) := by
    simp_rw [polarCoord_symm_eq_polarPt]
    exact (measurable_fst.ennreal_ofReal).smul
      ((hF.indicator measurableSet_ball).comp measurable_polarPt)
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hsplit : ∀ ρ ∈ Ioi (0 : ℝ),
      (∫⁻ t in Ioo (-π) π, ENNReal.ofReal (ρ, t).1 •
        (ball (0 : ℂ) 1).indicator F (Complex.polarCoord.symm (ρ, t))) =
      (Iio (1 : ℝ)).indicator
        (fun ρ => ENNReal.ofReal ρ * ∫⁻ t in Ioo (-π) π, F (polarPt ρ t)) ρ := by
    intro ρ hρ
    simp_rw [polarCoord_symm_eq_polarPt, smul_eq_mul]
    by_cases h1 : ρ < 1
    · rw [indicator_of_mem (show ρ ∈ Iio (1 : ℝ) from h1),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      rw [indicator_of_mem (polarPt_mem_ball (le_of_lt hρ) h1 t)]
    · rw [indicator_of_notMem (show ρ ∉ Iio (1 : ℝ) from h1)]
      refine (setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_).trans (lintegral_zero)
      rw [indicator_of_notMem, mul_zero]
      rw [mem_ball_zero_iff, norm_polarPt (le_of_lt hρ)]
      exact h1
  rw [setLIntegral_congr_fun measurableSet_Ioi hsplit, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]

/-! ## The `L²` coefficient bound (PU4) -/

/-- Parseval on the circle of radius `ρ`: `∑ |c_n|² ρ^{2|n|} = (2π)⁻¹ ∫₀^{2π} u(ρe^{it})² dt`. -/
theorem hasSum_sq_diskCoeff_pow {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1)) {u : ℂ → ℝ}
    (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z) (hcont : ContinuousOn u (ball 0 1)) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    HasSum (fun n : ℤ => ‖diskCoeff F n‖ ^ 2 * ρ ^ (2 * n.natAbs))
      ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, u (polarPt ρ t) ^ 2) := by
  have hφ : Continuous fun t : ℝ => (u (polarPt ρ t) : ℂ) := by
    refine Complex.continuous_ofReal.comp ?_
    refine hcont.comp_continuous (by unfold polarPt; fun_prop) fun t => polarPt_mem_ball hρ0 hρ1 t
  have h := hasSum_sq_circCoeff hφ
  have hcoef : ∀ n : ℤ, circCoeff (fun t : ℝ => (u (polarPt ρ t) : ℂ)) n =
      diskCoeff F n * (ρ : ℂ) ^ n.natAbs := by
    intro n
    rw [diskCoeff_mul_pow_eq hF hu hρ0 hρ1 n, circCoeff]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hint : ∀ t : ℝ, ‖(u (polarPt ρ t) : ℂ)‖ ^ 2 = u (polarPt ρ t) ^ 2 := fun t => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hint, hcoef] at h
  refine h.congr_fun fun n => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0, mul_pow,
    ← pow_mul, mul_comm n.natAbs 2]

/-- The circle integral as a lower integral over `(−π, π)`. -/
theorem lintegral_circle_sq_eq {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1)) {u : ℂ → ℝ}
    (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z) (hcont : ContinuousOn u (ball 0 1)) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∫⁻ t in Ioo (-π) π, ENNReal.ofReal (u (polarPt ρ t) ^ 2) =
      ENNReal.ofReal (2 * π * ∑' n : ℤ, ‖diskCoeff F n‖ ^ 2 * ρ ^ (2 * n.natAbs)) := by
  have hg : Continuous fun t : ℝ => u (polarPt ρ t) ^ 2 :=
    (hcont.comp_continuous (by unfold polarPt; fun_prop) fun t =>
      polarPt_mem_ball hρ0 hρ1 t).pow 2
  have hper : Function.Periodic (fun t : ℝ => u (polarPt ρ t) ^ 2) (2 * π) := by
    intro t
    simp only [polarPt]
    rw [show ((t + 2 * π : ℝ) : ℂ) * I = (t : ℂ) * I + 2 * π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hsum := (hasSum_sq_diskCoeff_pow hF hu hcont hρ0 hρ1).tsum_eq
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hg.integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self)
    (Eventually.of_forall fun t => sq_nonneg _), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  congr 1
  have h2 := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h2
  rw [h2, hsum]
  field_simp

/-- **(PU4).** If `u = Re F` is square integrable on the unit disk, then
`∑ |c_n|² / (|n| + 1) < ∞`. -/
theorem summable_sq_diskCoeff_div {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    {u : ℂ → ℝ} (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z) (hcont : ContinuousOn u (ball 0 1))
    (hL2 : ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (u z ^ 2) ≠ ⊤) :
    Summable fun n : ℤ => ‖diskCoeff F n‖ ^ 2 / (|(n : ℝ)| + 1) := by
  classical
  set L := ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (u z ^ 2)
  -- the integrand as a measurable function on `ℂ`
  set G : ℂ → ℝ≥0∞ := (ball (0 : ℂ) 1).indicator fun z => ENNReal.ofReal (u z ^ 2)
  have hGm : Measurable G := by
    have := ContinuousOn.measurable_piecewise (f := fun z => ENNReal.ofReal (u z ^ 2))
      (g := fun _ => (0 : ℝ≥0∞)) (s := ball (0 : ℂ) 1)
      (ENNReal.continuous_ofReal.comp_continuousOn (hcont.pow 2)) continuousOn_const
      measurableSet_ball
    have hG : G = (ball (0 : ℂ) 1).piecewise (fun z => ENNReal.ofReal (u z ^ 2)) fun _ => 0 := by
      funext z; simp only [G, Set.indicator, Set.piecewise]
    rw [hG]; exact this
  have hLG : L = ∫⁻ z in ball (0 : ℂ) 1, G z := by
    refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
    simp [G, indicator_of_mem hz]
  have hpolar := lintegral_ball_eq_polar hGm
  have key : ∀ S : Finset ℤ,
      ENNReal.ofReal (∑ n ∈ S, π * (‖diskCoeff F n‖ ^ 2 / (|(n : ℝ)| + 1))) ≤ L := by
    intro S
    rw [hLG, hpolar]
    have hpt : ∀ ρ ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (∑ n ∈ S,
        2 * π * ‖diskCoeff F n‖ ^ 2 * ρ ^ (2 * n.natAbs + 1)) ≤
        ENNReal.ofReal ρ * ∫⁻ t in Ioo (-π) π, G (polarPt ρ t) := by
      intro ρ hρ
      have hGρ : ∫⁻ t in Ioo (-π) π, G (polarPt ρ t) =
          ∫⁻ t in Ioo (-π) π, ENNReal.ofReal (u (polarPt ρ t) ^ 2) :=
        lintegral_congr fun t => by simp [G, indicator_of_mem (polarPt_mem_ball hρ.1.le hρ.2 t)]
      rw [hGρ, lintegral_circle_sq_eq hF hu hcont hρ.1.le hρ.2, ← ENNReal.ofReal_mul hρ.1.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hle := sum_le_hasSum S (fun n _ => mul_nonneg (sq_nonneg _) (pow_nonneg hρ.1.le _))
        (hasSum_sq_diskCoeff_pow hF hu hcont hρ.1.le hρ.2)
      rw [(hasSum_sq_diskCoeff_pow hF hu hcont hρ.1.le hρ.2).tsum_eq]
      calc ∑ n ∈ S, 2 * π * ‖diskCoeff F n‖ ^ 2 * ρ ^ (2 * n.natAbs + 1)
          = ρ * (2 * π * ∑ n ∈ S, ‖diskCoeff F n‖ ^ 2 * ρ ^ (2 * n.natAbs)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            ring
        _ ≤ ρ * (2 * π * ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, u (polarPt ρ t) ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by positivity)) hρ.1.le
    calc ENNReal.ofReal (∑ n ∈ S, π * (‖diskCoeff F n‖ ^ 2 / (|(n : ℝ)| + 1)))
        = ENNReal.ofReal (∫ ρ in Ioo (0 : ℝ) 1, ∑ n ∈ S,
            2 * π * ‖diskCoeff F n‖ ^ 2 * ρ ^ (2 * n.natAbs + 1)) := by
          congr 1
          rw [integral_finset_sum]
          · refine Finset.sum_congr rfl fun n _ => ?_
            rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
              ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
            have hn : |(n : ℝ)| = (n.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
            rw [hn]
            push_cast
            field_simp
            ring
          · intro n _
            exact (continuous_const.mul (continuous_pow _)).integrableOn_Icc.mono_set
              Ioo_subset_Icc_self
      _ = ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal (∑ n ∈ S,
            2 * π * ‖diskCoeff F n‖ ^ 2 * ρ ^ (2 * n.natAbs + 1)) := by
          refine ofReal_integral_eq_lintegral_ofReal ?_ ?_
          · exact (continuous_finsetSum _ fun n _ =>
              continuous_const.mul (continuous_pow _)).integrableOn_Icc.mono_set
              Ioo_subset_Icc_self
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
            exact Finset.sum_nonneg fun n _ => by have := hρ.1; positivity
      _ ≤ _ := setLIntegral_mono' measurableSet_Ioo hpt
  have hbound : ∀ S : Finset ℤ, ∑ n ∈ S, ‖diskCoeff F n‖ ^ 2 / (|(n : ℝ)| + 1) ≤ L.toReal / π := by
    intro S
    have h := key S
    rw [ENNReal.ofReal_le_iff_le_toReal hL2, ← Finset.mul_sum] at h
    rw [le_div_iff₀ Real.pi_pos]; linarith
  exact summable_of_sum_le (fun n => by positivity) hbound

end InteractingSLE.Sec6
