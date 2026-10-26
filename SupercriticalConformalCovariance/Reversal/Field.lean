import SupercriticalConformalCovariance.Reversal.Inverse
import SupercriticalConformalCovariance.Frozen.ConfPullbackField

set_option autoImplicit false
noncomputable section

open Set Function MeasureTheory TopologicalSpace
open scoped Distributions
open LQGMetric (DistOn TestOn)
open SmallGammaGeodesics.CC

namespace SupercriticalConformalCovariance.Reversal

open SupercriticalConformalCovariance

variable {φ : ℂ → ℂ} {U V : Opens ℂ}

private theorem logShift_locallyIntegrableOn (Q : ℝ)
    (hφ : IsConformalBijection φ U V) :
    LocallyIntegrableOn (fun x => Q * Real.log ‖deriv φ x‖) U volume := by
  have hd : ContinuousOn (deriv φ) U :=
    (hφ.1.deriv U.isOpen).continuousOn
  have hn : ContinuousOn (fun x => ‖deriv φ x‖) U :=
    continuous_norm.comp_continuousOn hd
  have hl : ContinuousOn (fun x => Real.log ‖deriv φ x‖) U := by
    exact Real.continuousOn_log.comp hn (fun x hx =>
      norm_ne_zero_iff.mpr
        (QuantumZipper.CA.deriv_ne_zero_of_injOn U.isOpen hφ.1 hφ.2.injOn hx))
  exact ((continuousOn_const.mul hl).locallyIntegrableOn U.isOpen.measurableSet)

private theorem inverse_shift_integral (Q : ℝ)
    (hφ : IsConformalBijection φ U V) (g : TestOn V) :
    (∫ x, (confPushTest (inverse_conformal hφ) g) x *
      (Q * Real.log ‖deriv φ x‖)) +
    (∫ y, g y * (Q * Real.log ‖deriv (invFunOn φ U) y‖)) = 0 := by
  let ψ : ℂ → ℂ := invFunOn φ U
  have hleft : ∀ x ∈ (U : Set ℂ), ψ (φ x) = x :=
    fun _ hx => hφ.2.injOn.leftInvOn_invFunOn hx
  have hzero : ∀ y ∉ φ '' (U : Set ℂ), (g : ℂ → ℝ) y = 0 := by
    intro y hy
    rw [hφ.2.image_eq] at hy
    exact g.zero_on_compl hy
  have hbase := integral_log_mul_confPullFun U.isOpen hφ.1 hφ.2.injOn hleft hzero
  have hpush := confPushTest_inverse_eq_confPullFun hφ g
  have hfirst :
      (∫ x, (confPushTest (inverse_conformal hφ) g) x *
        (Q * Real.log ‖deriv φ x‖)) =
      Q * ∫ x, Real.log ‖deriv φ x‖ * confPullFun φ U g x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [show (confPushTest (inverse_conformal hφ) g : ℂ → ℝ) x =
        confPullFun φ U g x from congrFun hpush x]
    ring
  have hsecond :
      (∫ y, g y * (Q * Real.log ‖deriv ψ y‖)) =
      Q * ∫ y, Real.log ‖deriv ψ y‖ * g y := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [hfirst, hsecond, hbase]
  ring

/-- Pulling a distribution to the source domain and back by the inverse restores it. -/
theorem confPullbackField_inverse (Q : ℝ)
    (hφ : IsConformalBijection φ U V) (h : DistOn V) :
    confPullbackField Q (inverse_conformal hφ) (confPullbackField Q hφ h) = h := by
  ext g
  have htest := confPushTest_inverse_right hφ g
  have hI := inverse_shift_integral Q hφ g
  have hlocφ := logShift_locallyIntegrableOn Q hφ
  have hlocψ := logShift_locallyIntegrableOn Q (inverse_conformal hφ)
  change h (confPushTest hφ (confPushTest (inverse_conformal hφ) g)) +
    Distribution.ofFun U (fun x => Q * Real.log ‖deriv φ x‖) volume ⊤
      (confPushTest (inverse_conformal hφ) g) +
    Distribution.ofFun V
      (fun y => Q * Real.log ‖deriv (invFunOn φ U) y‖) volume ⊤ g = h g
  rw [htest, Distribution.ofFun_apply hlocφ, Distribution.ofFun_apply hlocψ]
  simp only [smul_eq_mul]
  linarith

end SupercriticalConformalCovariance.Reversal
