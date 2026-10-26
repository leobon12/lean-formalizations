import SupercriticalConformalCovariance.ZBConformal.Setup
import SmallGammaGeodesics.CC.Pullback

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace
open LQGMetric (TestOn)
open SmallGammaGeodesics.CC

namespace SupercriticalConformalCovariance.BiLip.PortRev

open SupercriticalConformalCovariance

variable {φ : ℂ → ℂ} {U V : Opens ℂ}

/-- The inverse of a conformal bijection is a conformal bijection. -/
theorem inverse_conformal (hφ : IsConformalBijection φ U V) :
    IsConformalBijection (invFunOn φ U) V U := by
  have hleft : ∀ x ∈ (U : Set ℂ), invFunOn φ U (φ x) = x :=
    fun _ hx => hφ.2.injOn.leftInvOn_invFunOn hx
  constructor
  · simpa only [hφ.2.image_eq] using
      (differentiableOn_leftInv U.isOpen hφ.1 hφ.2.injOn hleft)
  · exact hφ.2.symm hφ.2.invOn_invFunOn.symm

/-- The inverse derivative times the forward derivative is one on the source domain. -/
theorem inverse_deriv_mul (hφ : IsConformalBijection φ U V)
    {x : ℂ} (hx : x ∈ U) :
    deriv (invFunOn φ U) (φ x) * deriv φ x = 1 := by
  exact deriv_leftInv_mul U.isOpen hφ.1 hφ.2.injOn
    (fun _ hz => hφ.2.injOn.leftInvOn_invFunOn hz) hx

/-- The two log Jacobians cancel pointwise. -/
theorem inverse_log_cancel (hφ : IsConformalBijection φ U V)
    {x : ℂ} (hx : x ∈ U) :
    Real.log ‖deriv (invFunOn φ U) (φ x)‖ + Real.log ‖deriv φ x‖ = 0 := by
  have hleft : ∀ z ∈ (U : Set ℂ), invFunOn φ U (φ z) = z :=
    fun _ hz => hφ.2.injOn.leftInvOn_invFunOn hz
  have h := log_norm_deriv_leftInv U.isOpen hφ.1 hφ.2.injOn hleft
    (Set.mem_image_of_mem φ hx)
  rw [hleft x hx] at h
  linarith

theorem confPullFun_congr_on {f g : ℂ → ℂ} {W : Opens ℂ}
    (heq : EqOn f g W) (t : ℂ → ℝ) :
    confPullFun f W t = confPullFun g W t := by
  funext x
  by_cases hx : x ∈ W
  · rw [confPullFun_of_mem hx, confPullFun_of_mem hx]
    have hderiv : deriv f x = deriv g x :=
      Filter.EventuallyEq.deriv_eq
        (Filter.eventuallyEq_of_mem (W.isOpen.mem_nhds hx) heq)
    rw [hderiv, heq hx]
  · rw [confPullFun_of_notMem hx, confPullFun_of_notMem hx]

theorem inverse_inverse_eqOn (hφ : IsConformalBijection φ U V) :
    EqOn (invFunOn (invFunOn φ U) V) φ U := by
  intro x hx
  have hy : φ x ∈ V := hφ.2.mapsTo hx
  have h := (inverse_conformal hφ).2.injOn.leftInvOn_invFunOn hy
  simpa only [hφ.2.injOn.leftInvOn_invFunOn hx] using h

/-- The inverse map's test pushforward is the conformal pullback along the forward map. -/
theorem confPushTest_inverse_eq_confPullFun
    (hφ : IsConformalBijection φ U V) (g : TestOn V) :
    (confPushTest (inverse_conformal hφ) g : ℂ → ℝ) =
      confPullFun φ U g := by
  change confPullFun (invFunOn (invFunOn φ U) V) U g = _
  exact confPullFun_congr_on (inverse_inverse_eqOn hφ) g

/-- Forward test transport followed by inverse transport is the identity. -/
theorem confPushTest_inverse_left (hφ : IsConformalBijection φ U V)
    (g : TestOn U) :
    confPushTest (inverse_conformal hφ) (confPushTest hφ g) = g := by
  let ψ : ℂ → ℂ := invFunOn φ U
  ext x
  change confPullFun (invFunOn ψ V) U (confPullFun ψ V g) x = g x
  rw [confPullFun_congr_on (inverse_inverse_eqOn hφ) (confPullFun ψ V g)]
  have hleft : ∀ z ∈ (U : Set ℂ), ψ (φ z) = z :=
    fun _ hz => hφ.2.injOn.leftInvOn_invFunOn hz
  rw [show (V : Set ℂ) = φ '' U from hφ.2.image_eq.symm]
  rw [confPullFun_confPullFun_leftInv U.isOpen hφ.1 hφ.2.injOn hleft]
  by_cases hx : x ∈ U
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport (fun ht => hx (g.tsupport_subset ht))).symm

/-- Inverse test transport followed by forward transport is the identity. -/
theorem confPushTest_inverse_right (hφ : IsConformalBijection φ U V)
    (g : TestOn V) :
    confPushTest hφ (confPushTest (inverse_conformal hφ) g) = g := by
  let ψ : ℂ → ℂ := invFunOn φ U
  ext y
  change confPullFun ψ V (confPullFun (invFunOn ψ V) U g) y = g y
  rw [confPullFun_congr_on (inverse_inverse_eqOn hφ) g]
  have hleft : ∀ z ∈ (U : Set ℂ), ψ (φ z) = z :=
    fun _ hz => hφ.2.injOn.leftInvOn_invFunOn hz
  rw [show (V : Set ℂ) = φ '' U from hφ.2.image_eq.symm]
  rw [confPullFun_leftInv_confPullFun U.isOpen hφ.1 hφ.2.injOn hleft]
  by_cases hy : y ∈ φ '' U
  · exact indicator_of_mem hy _
  · rw [indicator_of_notMem hy]
    exact (image_eq_zero_of_notMem_tsupport (fun ht =>
      (fun hv => hy (hφ.2.surjOn hv)) (g.tsupport_subset ht))).symm

end SupercriticalConformalCovariance.BiLip.PortRev
