import HigherDimLQGContinuity.ConvTransfer.Model
import HigherDimLFPP.Field.Measures
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quantitative Gaussian corrections in the real-cutoff transfer

Elementary band variance estimates precede the compact-supremum estimates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The finite logarithmic band paired with a difference of probability measures
has variance at most four times its logarithmic width. -/
theorem convEnv_finiteBand_var_le_log {d : ℕ} {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {R : ℝ} (hR : 1 ≤ R) :
    ‖HigherDimLFPP.bandVecM κ (Ioc 1 R) μ ν‖ ^ 2 ≤ 4 * Real.log R := by
  have hp : HigherDimLFPP.IsPairable κ (Ioc 1 R) μ ν :=
    HigherDimLFPP.isPairable_of_subset_Icc hκ measurableSet_Ioc one_pos
      (fun t ht => ⟨ht.1.le, ht.2⟩) μ ν
  have hS0 : Ioc (1 : ℝ) R ⊆ Ioi (0 : ℝ) :=
    fun t ht => one_pos.trans ht.1
  have hi : IntegrableOn (fun t : ℝ => 4 * t⁻¹) (Ioc 1 R) := by
    have hc : ContinuousOn (fun t : ℝ => 4 * t⁻¹) (Icc 1 R) := by
      fun_prop (disch := intro t ht; have := ht.1; positivity)
    exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hpt : ∀ t ∈ Ioc (1 : ℝ) R,
      HigherDimLFPP.scalePair κ t μ ν μ ν ≤ 4 * t⁻¹ := by
    intro t ht
    have h := HigherDimLFPP.abs_scalePair_le hκ (one_pos.trans ht.1) μ ν μ ν
    have hraw := (le_abs_self (HigherDimLFPP.scalePair κ t μ ν μ ν)).trans h
    simp only [probReal_univ] at hraw
    have hval : t⁻¹ * (((1 : ℝ) + 1) * (1 + 1)) = 4 * t⁻¹ := by ring
    rw [hval] at hraw
    exact hraw
  calc
    ‖HigherDimLFPP.bandVecM κ (Ioc 1 R) μ ν‖ ^ 2 =
        HigherDimLFPP.scaleCov κ (Ioc 1 R) μ ν μ ν :=
      (HigherDimLFPP.scaleCov_self (Ioc 1 R) μ ν).symm
    _ = ∫ t in Ioc (1 : ℝ) R, HigherDimLFPP.scalePair κ t μ ν μ ν :=
      HigherDimLFPP.scaleCov_eq_integral hκ measurableSet_Ioc hS0 hp hp
    _ ≤ ∫ t in Ioc (1 : ℝ) R, 4 * t⁻¹ :=
      setIntegral_mono_on (HigherDimLFPP.integrableOn_scalePair hκ measurableSet_Ioc hS0 hp hp)
        hi measurableSet_Ioc hpt
    _ = 4 * Real.log R := by
      rw [← intervalIntegral.integral_of_le hR, intervalIntegral.integral_const_mul,
        integral_inv_of_pos one_pos (by linarith : 0 < R)]
      simp

/-- The far part of the centered infrared correction has bounded variance
uniformly on a ball whose radius is the lower scale cutoff. -/
theorem convEnv_highBand_var_le {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ}, 1 ≤ R → ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      ‖HigherDimLFPP.bandVecM κ (Ioi R) (Measure.dirac x) (unitSphereProb d)‖ ^ 2 ≤ C := by
  obtain ⟨L, hL0, hL⟩ := HigherDimLFPP.exists_one_sub_autoCorr_le hκ
  let v₀ := HigherDimLFPP.bandVecM κ (Ioi 1)
    (Measure.dirac (0 : Rd d)) (unitSphereProb d)
  let C : ℝ := 2 * ‖v₀‖ ^ 2 + 2 * L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR x hx
  have hR0 : 0 < R := by linarith
  let vx := HigherDimLFPP.bandVecM κ (Ioi R) (Measure.dirac x) (unitSphereProb d)
  let vz := HigherDimLFPP.bandVecM κ (Ioi R)
    (Measure.dirac (0 : Rd d)) (unitSphereProb d)
  have hp1 := HigherDimLQGMetric.l6a_isPairable_centeredIoi hd hκ one_pos
    (0 : Rd d)
  have hvar0 : ‖vz‖ ^ 2 ≤ ‖v₀‖ ^ 2 := by
    have hsub : Ioi R ⊆ Ioi (1 : ℝ) := fun t ht => hR.trans_lt ht
    have h := HigherDimLFPP.scaleCov_self_le_of_subset measurableSet_Ioi hsub hp1
    simpa only [HigherDimLFPP.scaleCov_self, vz, v₀] using h
  have hdiff : ‖vx - vz‖ ^ 2 ≤ L := by
    have h := HigherDimLQGMetric.l6a_norm_centeredIoi_sub_sq_le hκ
      (fun v => (hL v).2) hR0 x 0
    have heq := HigherDimLQGMetric.l6a_centeredIoi_sub hd hκ hR0 x 0
    rw [← heq] at h
    have hxR : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hx
    have hsq : ‖x‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg x) hR0.le).2 hxR
    have hval : L * ‖x‖ ^ 2 / R ^ 2 ≤ L := by
      apply (div_le_iff₀ (sq_pos_of_pos hR0)).2
      exact mul_le_mul_of_nonneg_left hsq hL0
    simp only [sub_zero] at h
    change ‖vx - vz‖ ^ 2 ≤ L * ‖x‖ ^ 2 / R ^ 2 at h
    exact h.trans hval
  have htri := norm_add_le (vx - vz) vz
  have heq : (vx - vz) + vz = vx := by abel
  rw [heq] at htri
  have hsq : ‖vx‖ ^ 2 ≤ 2 * ‖vx - vz‖ ^ 2 + 2 * ‖vz‖ ^ 2 := by
    nlinarith [sq_nonneg (‖vx - vz‖ - ‖vz‖), norm_nonneg vx,
      norm_nonneg (vx - vz), norm_nonneg vz]
  change ‖vx‖ ^ 2 ≤ C
  dsimp [C]
  nlinarith only [hsq, hdiff, hvar0]

/-- The full infrared correction has logarithmic point variance. -/
theorem convEnv_infrared_var_le_log {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ}, 1 ≤ R → ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      ‖HigherDimLFPP.bandVecM κ (Ioi 1) (Measure.dirac x) (unitSphereProb d)‖ ^ 2 ≤
        C * (1 + Real.log R) := by
  letI : IsProbabilityMeasure (unitSphereProb d) :=
    isProbabilityMeasure_unitSphereProb (by omega : 1 ≤ d)
  obtain ⟨C₀, hC₀, hhigh⟩ := convEnv_highBand_var_le hd hκ
  let C : ℝ := 8 + 2 * C₀
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR x hx
  let μ : Measure (Rd d) := Measure.dirac x
  let ν : Measure (Rd d) := unitSphereProb d
  let vlo := HigherDimLFPP.bandVecM κ (Ioc 1 R) μ ν
  let vhi := HigherDimLFPP.bandVecM κ (Ioi R) μ ν
  let vall := HigherDimLFPP.bandVecM κ (Ioi 1) μ ν
  have hpair : HigherDimLFPP.IsPairable κ (Ioi 1) μ ν :=
    l6a_isPairable_centeredIoi hd hκ one_pos x
  have hset : Ioc (1 : ℝ) R ∪ Ioi R = Ioi 1 := Ioc_union_Ioi_eq_Ioi hR
  have hpairU : HigherDimLFPP.IsPairable κ (Ioc (1 : ℝ) R ∪ Ioi R) μ ν :=
    hset ▸ hpair
  have hsum : vall = vlo + vhi := by
    have h := HigherDimLFPP.bandVecM_union measurableSet_Ioc measurableSet_Ioi
      Ioc_disjoint_Ioi_same hpairU
    simpa only [hset, vall, vlo, vhi] using h
  have hlow : ‖vlo‖ ^ 2 ≤ 4 * Real.log R :=
    convEnv_finiteBand_var_le_log hκ μ ν hR
  have hhi : ‖vhi‖ ^ 2 ≤ C₀ := hhigh hR x hx
  have hnorm := norm_add_le vlo vhi
  rw [← hsum] at hnorm
  have hsq : ‖vall‖ ^ 2 ≤ 2 * ‖vlo‖ ^ 2 + 2 * ‖vhi‖ ^ 2 := by
    nlinarith [sq_nonneg (‖vlo‖ - ‖vhi‖), norm_nonneg vall,
      norm_nonneg vlo, norm_nonneg vhi]
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR
  change ‖vall‖ ^ 2 ≤ C * (1 + Real.log R)
  dsimp [C]
  nlinarith only [hsq, hlow, hhi, hC₀, hlog]

/-- The infrared correction has unit-scale Lipschitz canonical metric. -/
theorem convEnv_infrared_incr_le {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ L : ℝ, 0 < L ∧ ∀ x y : Rd d,
      ‖HigherDimLFPP.bandVecM κ (Ioi 1) (Measure.dirac x) (unitSphereProb d) -
        HigherDimLFPP.bandVecM κ (Ioi 1) (Measure.dirac y) (unitSphereProb d)‖ ^ 2 ≤
          L * ‖x - y‖ ^ 2 := by
  obtain ⟨L₀, hL₀, hL⟩ := HigherDimLFPP.exists_one_sub_autoCorr_le hκ
  let L : ℝ := max 1 L₀
  have hLp : 0 < L := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨L, hLp, ?_⟩
  intro x y
  have h := HigherDimLQGMetric.l6a_norm_centeredIoi_sub_sq_le hκ
    (fun v => (hL v).2) one_pos x y
  rw [← HigherDimLQGMetric.l6a_centeredIoi_sub hd hκ one_pos x y] at h
  simp only [one_pow, div_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))

end HigherDimLQGContinuity
