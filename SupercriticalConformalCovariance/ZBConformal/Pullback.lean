import SupercriticalConformalCovariance.ZBConformal.Setup
import LQGMetric.Field.ZeroBoundary

set_option autoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace Set Function
open scoped Distributions

namespace SupercriticalConformalCovariance.ZBConformal
open SupercriticalConformalCovariance
open LQGMetric
open SmallGammaGeodesics.CC

/-- Pullback of a distribution by a conformal bijection, using the candidate test transport. -/
def distPullback {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (h : DistOn V) : DistOn U :=
  (confPushTest hφ).precompCompactConvergenceCLM ℝ h

@[simp] theorem distPullback_apply {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (h : DistOn V) (ψ : TestOn U) :
    distPullback hφ h ψ = h (confPushTest hφ ψ) := rfl

/-- Conformal substitution for the transported test function. The function `u` is arbitrary. -/
theorem integral_mul_confPushTest {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (ψ : TestOn U) (u : ℂ → ℝ) :
    ∫ y, u y * (confPushTest hφ ψ) y = ∫ x, u (φ x) * ψ x := by
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
  have hzero : ∀ x ∉ inv '' (V : Set ℂ), (ψ : ℂ → ℝ) x = 0 := by
    intro x hx
    apply ψ.zero_on_compl
    rw [himage] at hx
    exact hx
  have h := integral_confPullFun_mul V.isOpen hdiff hinj hφψ hzero u
  change (∫ y, confPullFun inv V ψ y * u y) = _ at h
  calc
    (∫ y, u y * (confPushTest hφ ψ) y) = ∫ y, confPullFun inv V ψ y * u y := by
      congr 1; funext y; change u y * confPullFun inv V ψ y = _; ring
    _ = ∫ x, ψ x * u (φ x) := h
    _ = ∫ x, u (φ x) * ψ x := by congr 1; funext x; ring

/-- Measurability for the cylinder σ-algebras. -/
theorem measurable_distPullback {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) : Measurable (distPullback hφ) := by
  apply measurable_distOn_iff.mpr
  intro ψ
  exact measurable_distOn_apply (confPushTest hφ ψ)

end SupercriticalConformalCovariance.ZBConformal
