import SupercriticalConformalCovariance.ZBConformal.Pullback

set_option autoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace Set Function
open SmallGammaGeodesics.CC
open LQGMetric
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.ZBConformal

/-- The Jacobian transport commutes with positive part. -/
theorem max_confPushTest {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (ψ : TestOn U) (y : ℂ) :
    max ((confPushTest hφ ψ) y) 0 =
      confPullFun (invFunOn φ U) V (fun x => max (ψ x) 0) y := by
  by_cases hy : y ∈ (V : Set ℂ)
  · change max (confPullFun (invFunOn φ U) V ψ y) 0 = _
    rw [confPullFun_of_mem hy, confPullFun_of_mem hy]
    rw [mul_max_of_nonneg _ _ (sq_nonneg _), mul_zero]
  · change max (confPullFun (invFunOn φ U) V ψ y) 0 = _
    rw [confPullFun_of_notMem hy, confPullFun_of_notMem hy]
    simp

/-- The transport also commutes with negative part. -/
theorem max_neg_confPushTest {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (ψ : TestOn U) (y : ℂ) :
    max (-(confPushTest hφ ψ) y) 0 =
      confPullFun (invFunOn φ U) V (fun x => max (-ψ x) 0) y := by
  by_cases hy : y ∈ (V : Set ℂ)
  · change max (-(confPullFun (invFunOn φ U) V ψ y)) 0 = _
    rw [confPullFun_of_mem hy, confPullFun_of_mem hy]
    rw [← mul_neg, mul_max_of_nonneg _ _ (sq_nonneg _), mul_zero]
  · change max (-(confPullFun (invFunOn φ U) V ψ y)) 0 = _
    rw [confPullFun_of_notMem hy, confPullFun_of_notMem hy]
    simp


/-- Positive test-density substitution, including the conformal Jacobian. -/
theorem integral_max_confPushTest {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (ψ : TestOn U) (u : ℂ → ℝ) :
    ∫ y, max ((confPushTest hφ ψ) y) 0 * u y =
      ∫ x, max (ψ x) 0 * u (φ x) := by
  let inv := invFunOn φ (U : Set ℂ)
  have hψφ : ∀ x ∈ (U : Set ℂ), inv (φ x) = x :=
    fun _ hx => hφ.2.injOn.leftInvOn_invFunOn hx
  have hφψ : ∀ y ∈ (V : Set ℂ), φ (inv y) = y := by
    intro y hy
    exact apply_leftInv hψφ (hφ.2.image_eq.symm ▸ hy)
  have hdiff : DifferentiableOn ℂ inv V := by
    have h := differentiableOn_leftInv U.isOpen hφ.1 hφ.2.injOn hψφ
    rwa [hφ.2.image_eq] at h
  have hinj : InjOn inv V := by
    have h := injOn_leftInv hψφ
    rwa [hφ.2.image_eq] at h
  have himage : inv '' (V : Set ℂ) = (U : Set ℂ) := by
    rw [← hφ.2.image_eq, image_leftInv_image hψφ subset_rfl]
  have hzero : ∀ x ∉ inv '' (V : Set ℂ), max (ψ x) 0 = 0 := by
    intro x hx
    rw [himage] at hx
    rw [ψ.zero_on_compl hx]
    simp
  have h := integral_confPullFun_mul V.isOpen hdiff hinj hφψ hzero u
  simp_rw [max_confPushTest hφ ψ]
  exact h

/-- Negative test-density substitution, including the conformal Jacobian. -/
theorem integral_max_neg_confPushTest {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (ψ : TestOn U) (u : ℂ → ℝ) :
    ∫ y, max (-(confPushTest hφ ψ) y) 0 * u y =
      ∫ x, max (-ψ x) 0 * u (φ x) := by
  let inv := invFunOn φ (U : Set ℂ)
  have hψφ : ∀ x ∈ (U : Set ℂ), inv (φ x) = x :=
    fun _ hx => hφ.2.injOn.leftInvOn_invFunOn hx
  have hφψ : ∀ y ∈ (V : Set ℂ), φ (inv y) = y := by
    intro y hy
    exact apply_leftInv hψφ (hφ.2.image_eq.symm ▸ hy)
  have hdiff : DifferentiableOn ℂ inv V := by
    have h := differentiableOn_leftInv U.isOpen hφ.1 hφ.2.injOn hψφ
    rwa [hφ.2.image_eq] at h
  have hinj : InjOn inv V := by
    have h := injOn_leftInv hψφ
    rwa [hφ.2.image_eq] at h
  have himage : inv '' (V : Set ℂ) = (U : Set ℂ) := by
    rw [← hφ.2.image_eq, image_leftInv_image hψφ subset_rfl]
  have hzero : ∀ x ∉ inv '' (V : Set ℂ), max (-ψ x) 0 = 0 := by
    intro x hx
    rw [himage] at hx
    rw [ψ.zero_on_compl hx]
    simp
  have h := integral_confPullFun_mul V.isOpen hdiff hinj hφψ hzero u
  simp_rw [max_neg_confPushTest hφ ψ]
  exact h

end SupercriticalConformalCovariance.ZBConformal
