import SupercriticalConformalCovariance.TV.EnergyMoments
import LQGMetric.Papers.GM.S2.SpatialIndepRad

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set LQGMetric QuantumZipper LQGMetric.GM

namespace SupercriticalConformalCovariance.TV

def spatialIncrementIntegral (R : ℝ) (T : DistC) : ℝ :=
  ∫ y in closedBall (0 : ℂ) (2 * R + 4),
    |rawCenteredRepresentative (1 / 4) (by norm_num) T y|

theorem measurable_spatialIncrementIntegral (R : ℝ) :
    Measurable (spatialIncrementIntegral R) := by
  have hm : Measurable (fun p : DistC × ℂ =>
      |rawCenteredRepresentative (1 / 4) (by norm_num) p.1 p.2|) :=
    continuous_abs.measurable.comp
      (measurable_rawCenteredRepresentative (1 / 4) (by norm_num))
  exact hm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℂ).restrict (closedBall (0 : ℂ) (2 * R + 4))) |>.measurable

theorem spatialIncrementIntegral_nonneg (R : ℝ) (T : DistC) :
    0 ≤ spatialIncrementIntegral R T :=
  integral_nonneg fun _ => abs_nonneg _

/-- Mean-value control of every point in the cutoff neighborhood by one spatial integral. -/
theorem harmonic_increment_le_spatial_integral
    (R L : ℝ) (hR : 0 < R) (hL : 2 * R + 5 < L)
    (D : TopologicalSpace.Opens ℂ) (hBD : ball (0 : ℂ) L ⊆ D)
    {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g D)
    (T : DistC) (hT : ∀ φ : TestOn D,
      restrictTo D T φ = ∫ y, g y * φ y)
    {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) (2 * R + 3)) :
    |g x - g 0| ≤
      (expNegInvGlue ((1 / 2 : ℝ) ^ 2) / (∫ y, radProf (1 / 2) y)) *
        spatialIncrementIntegral R T := by
  let K : Set ℂ := closedBall (0 : ℂ) (2 * R + 4)
  have hK_D : K ⊆ D := by
    intro y hy
    apply hBD
    rw [mem_ball, dist_zero_right]
    have hyn : ‖y‖ ≤ 2 * R + 4 := by simpa [K, mem_closedBall, dist_zero_right] using hy
    linarith
  have hB : closedBall x (1 / 2 : ℝ) ⊆ K := by
    intro y hy
    have hxy : ‖y - x‖ ≤ (1 / 2 : ℝ) := by
      simpa [mem_closedBall, dist_eq_norm] using hy
    have hxn : ‖x‖ ≤ 2 * R + 3 := by
      simpa [mem_closedBall, dist_zero_right] using hx
    have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (y - x) x
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hcont : ContinuousOn (fun y => |g y - g 0|) K := by
    intro y hy
    exact (((hg y (hK_D hy)).1.continuousAt.sub continuousAt_const).abs).continuousWithinAt
  have hint : IntegrableOn (fun y => |g y - g 0|) K :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  have hmono : (∫ y in closedBall x (1 / 2 : ℝ), |g y - g 0|) ≤
      ∫ y in K, |g y - g 0| :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hB)
  have hC : 0 ≤ expNegInvGlue ((1 / 2 : ℝ) ^ 2) / (∫ y, radProf (1 / 2) y) := by
    exact div_nonneg (expNegInvGlue.nonneg _) (integral_radProf_pos (by norm_num)).le
  have hmean := abs_sub_le_integral_of_harmonic D.isOpen hg (by norm_num : (0:ℝ)<1/2)
    (hB.trans hK_D) (g 0)
  have hstep := hmean.trans (mul_le_mul_of_nonneg_left hmono hC)
  have hpoint : ∀ y ∈ K,
      rawCenteredRepresentative (1 / 4) (by norm_num) T y = g y - g 0 := by
    intro y hy
    have hyn : ‖y‖ ≤ 2 * R + 4 := by simpa [K, mem_closedBall, dist_zero_right] using hy
    have hBy : closedBall y (1 / 4 : ℝ) ⊆ D := by
      intro w hw
      apply hBD
      rw [mem_ball, dist_zero_right]
      have hwy : ‖w - y‖ ≤ (1 / 4 : ℝ) := by
        simpa [mem_closedBall, dist_eq_norm] using hw
      have htri : ‖w‖ ≤ ‖w - y‖ + ‖y‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w - y) y
      linarith
    have hB0 : closedBall (0 : ℂ) (1 / 4 : ℝ) ⊆ D := by
      intro w hw
      apply hBD
      rw [mem_ball, dist_zero_right]
      have hwn : ‖w‖ ≤ (1 / 4 : ℝ) := by
        simpa [mem_closedBall, dist_zero_right] using hw
      linarith
    exact rawCenteredRepresentative_eq_of_harmonic hg hT (by norm_num) hBy hB0
  have heq : spatialIncrementIntegral R T = ∫ y in K, |g y - g 0| := by
    exact setIntegral_congr_fun measurableSet_closedBall (fun y hy =>
      congrArg abs (hpoint y hy))
  rw [← heq] at hstep
  exact hstep

end SupercriticalConformalCovariance.TV
