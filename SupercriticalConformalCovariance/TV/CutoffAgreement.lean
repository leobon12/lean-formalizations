import SupercriticalConformalCovariance.TV.CutoffSmooth
import LQGMetric.Papers.GM.S2.SpatialIndepAsm1

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set LQGMetric QuantumZipper QuantumZipper.K3
open scoped Convolution

namespace SupercriticalConformalCovariance.TV

theorem rawCenteredRepresentative_eq_of_harmonic
    {D : TopologicalSpace.Opens ℂ} {g : ℂ → ℝ} {T : DistC}
    (hg : InnerProductSpace.HarmonicOnNhd g D)
    (hT : ∀ φ : TestOn D, restrictTo D T φ = ∫ x, g x * φ x)
    {δ : ℝ} (hδ : 0 < δ) {x : ℂ}
    (hx : closedBall x δ ⊆ D)
    (h0 : closedBall (0 : ℂ) δ ⊆ D) :
    rawCenteredRepresentative δ hδ T x = g x - g 0 := by
  simp only [rawCenteredRepresentative,
    radialRepresentative_eq_of_harmonic hg hT hδ hx,
    radialRepresentative_eq_of_harmonic hg hT hδ h0]

/-- On the cutoff support, the canonical smooth extension equals the harmonic increment. -/
theorem smoothedRepresentative_eq_of_harmonic
    {R L : ℝ} (hR : 0 < R) (hL : 2 * R + 4 < L)
    {D : TopologicalSpace.Opens ℂ} (hBD : ball (0 : ℂ) L ⊆ D)
    {g : ℂ → ℝ} {T : DistC}
    (hg : InnerProductSpace.HarmonicOnNhd g D)
    (hT : ∀ φ : TestOn D, restrictTo D T φ = ∫ x, g x * φ x)
    {x : ℂ} (hx : ‖x‖ ≤ 2 * R + 2) :
    smoothedRepresentative R hR (1 / 4) (1 / 4) (by norm_num) T x =
      g x - g 0 := by
  let ε : ℝ := 1 / 4
  have hε : 0 < ε := by norm_num [ε]
  have h0 : closedBall (0 : ℂ) ε ⊆ D :=
    (closedBall_subset_ball_zero_of_norm_add_lt (y := (0 : ℂ)) (by
      simp only [norm_zero, zero_add]; dsimp [ε]; linarith)).trans hBD
  have hinner (t : ℂ) (ht : ‖t‖ ≤ 2 * R + 3) : closedBall t ε ⊆ D :=
    (closedBall_subset_ball_zero_of_norm_add_lt (y := t) (by dsimp [ε]; linarith)).trans hBD
  have hη (t : ℂ) (ht : ‖t‖ ≤ 2 * R + 3) : outerCutoff R hR t = 1 :=
    (outerCutoff R hR).one_of_mem_closedBall (by
      rw [mem_closedBall, dist_zero_right]
      simpa [outerCutoff] using ht)
  have hconv :
      ((fun t => outerCutoff R hR t * rawCenteredRepresentative ε hε T t)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (rbump 0 ε)) x =
      ∫ t, (g t - g 0) * rbump 0 ε (x - t) := by
    rw [convolution_def]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    by_cases ht : ‖x - t‖ < ε
    · have htn : ‖t‖ ≤ 2 * R + 3 := by
        have htri : ‖t‖ ≤ ‖t - x‖ + ‖x‖ := by
          simpa only [sub_add_cancel] using norm_add_le (t - x) x
        rw [norm_sub_rev] at htri
        dsimp [ε] at ht
        linarith
      rw [hη t htn, one_mul,
        rawCenteredRepresentative_eq_of_harmonic hg hT hε (hinner t htn) h0]
    · have hzero : rbump (0 : ℂ) ε (x - t) = 0 :=
        rbump_eq_zero hε (by simpa using (not_lt.mp ht))
      simp [hzero]
  have htrans :
      (∫ t, (g t - g 0) * rbump 0 ε (x - t)) =
      ∫ t, (g (x + t) - g 0) * rbump 0 ε t := by
    calc
      _ = ∫ t, (g (x + t) - g 0) * rbump 0 ε (x - (x + t)) := by
        rw [integral_add_left_eq_self (fun t => (g t - g 0) * rbump 0 ε (x - t)) x]
      _ = _ := by
        congr 1; funext t
        simp [rbump, norm_neg]
  have hxb : closedBall x ε ⊆ D :=
    hinner x (by linarith)
  have hgrad : InnerProductSpace.HarmonicOnNhd (fun t => g t - g 0) D :=
    hg.sub (InnerProductSpace.harmonicOnNhd_const _)
  have hmv :
      (∫ t, (g (x + t) - g 0) * rbump 0 ε t) =
      (g x - g 0) * ∫ t, rbump 0 ε t := by
    apply LQGMetric.GM.integral_mul_radial_of_harmonic D.isOpen hgrad hxb
      (contDiff_rbump 0 ε (n := 0)).continuous
      (fun t ht => rbump_eq_zero hε (by simpa only [sub_zero] using ht.le))
    intro a t
    simp [rbump]
  have hI : (∫ t, rbump (0 : ℂ) ε t) ≠ 0 :=
    (integral_pos_of_pos_on_ball (contDiff_rbump 0 ε (n := 0)).continuous
      (hasCompactSupport_rbump hε) (rbump_nonneg 0 ε) hε
      (fun t ht => rbump_pos hε ht)).ne'
  change (∫ t, rbump (0 : ℂ) ε t)⁻¹ *
      ((fun t => outerCutoff R hR t * rawCenteredRepresentative ε hε T t)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (rbump 0 ε)) x = _
  rw [hconv, htrans, hmv, mul_comm (g x - g 0), ← mul_assoc,
    inv_mul_cancel₀ hI, one_mul]

theorem smoothCutoffShift_eq_of_harmonic
    {R L : ℝ} (hR : 0 < R) (hL : 2 * R + 4 < L)
    {D : TopologicalSpace.Opens ℂ} (hBD : ball (0 : ℂ) L ⊆ D)
    {g : ℂ → ℝ} {T : DistC}
    (hg : InnerProductSpace.HarmonicOnNhd g D)
    (hT : ∀ φ : TestOn D, restrictTo D T φ = ∫ x, g x * φ x)
    (x : ℂ) :
    smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) T x =
      innerCutoff R hR x * (g x - g 0) := by
  by_cases hx : ‖x‖ ≤ 2 * R + 2
  · rw [smoothCutoffShift,
      smoothedRepresentative_eq_of_harmonic hR hL hBD hg hT hx]
  · have hχ : innerCutoff R hR x = 0 :=
      (innerCutoff R hR).zero_of_le_dist (by
        rw [dist_zero_right]
        simpa [innerCutoff] using (not_le.mp hx).le)
    simp [smoothCutoffShift, hχ]

theorem smoothCutoffShift_eq_increment_on_ball
    {R L : ℝ} (hR : 0 < R) (hL : 2 * R + 4 < L)
    {D : TopologicalSpace.Opens ℂ} (hBD : ball (0 : ℂ) L ⊆ D)
    {g : ℂ → ℝ} {T : DistC}
    (hg : InnerProductSpace.HarmonicOnNhd g D)
    (hT : ∀ φ : TestOn D, restrictTo D T φ = ∫ x, g x * φ x)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) (R + 1)) :
    smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) T x =
      g x - g 0 := by
  rw [smoothCutoffShift_eq_of_harmonic hR hL hBD hg hT,
    innerCutoff_eq_one R hR (mem_closedBall.2 (mem_ball.1 hx).le), one_mul]

theorem smoothCutoffShift_pair_eq_harmonic_pair
    {R L : ℝ} (hR : 0 < R) (hL : 2 * R + 4 < L)
    {D : TopologicalSpace.Opens ℂ} (hBD : ball (0 : ℂ) L ⊆ D)
    {g : ℂ → ℝ} {T : DistC}
    (hg : InnerProductSpace.HarmonicOnNhd g D)
    (hT : ∀ φ : TestOn D, restrictTo D T φ = ∫ x, g x * φ x)
    (ψ : TestOn D) (hψR : tsupport (ψ : ℂ → ℝ) ⊆ ball (0 : ℂ) R)
    (hψ0 : ∫ x, ψ x = 0) :
    ∫ x, smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) T x * ψ x =
      restrictTo D T ψ := by
  have heq :
      (∫ x, smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) T x * ψ x) =
      ∫ x, (g x - g 0) * ψ x := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : ψ x = 0
    · simp [hx]
    · have hxR : x ∈ ball (0 : ℂ) R := hψR (subset_tsupport _ hx)
      change smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) T x * ψ x =
        (g x - g 0) * ψ x
      rw [smoothCutoffShift_eq_increment_on_ball hR hL hBD hg hT
        (ball_subset_ball (by linarith) hxR)]
  rw [heq]
  have hgc : ∀ x ∈ (D : Set ℂ), ContinuousAt g x :=
    fun x hx => (hg x hx).1.continuousAt
  have hintg := LQGMetric.GM.integrable_mul_testOn hgc ψ
  have hintψ : Integrable (fun x => ψ x) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hfun : (fun x => (g x - g 0) * ψ x) =
      (fun x => g x * ψ x - g 0 * ψ x) := by funext x; ring
  rw [hfun, integral_sub hintg (hintψ.const_mul (g 0)), integral_const_mul,
    hψ0, mul_zero, sub_zero, ← hT]

end SupercriticalConformalCovariance.TV
