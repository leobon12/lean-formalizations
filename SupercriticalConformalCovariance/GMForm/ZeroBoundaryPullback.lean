import SupercriticalConformalCovariance.GMForm.ZeroBoundary
import SupercriticalConformalCovariance.Root.Field
import SupercriticalConformalCovariance.GPull.Correction

set_option autoImplicit false
noncomputable section

open MeasureTheory TopologicalSpace Set Function
open LQGMetric (DistOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GMForm

/-- The continuous correction in GM's forward coordinate convention. -/
def gmCorrection (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (f : C(U, ℝ)) : C(V, ℝ) :=
  f.comp (SupercriticalConformalCovariance.Root.mapsToCM (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)) +
    SupercriticalConformalCovariance.GPull.logDerivCont Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)

theorem measurable_gmCorrection (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] {f : Ω → C(U, ℝ)} (hf : Measurable f) :
    Measurable fun ω => gmCorrection Q hφ (f ω) := by
  have : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  rw [ContinuousMap.measurable_iff_eval]
  intro x
  change Measurable fun ω =>
    f ω (SupercriticalConformalCovariance.Root.mapsToCM (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) x) +
      SupercriticalConformalCovariance.GPull.logDerivCont Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) x
  exact ((ContinuousMap.measurable_eval _).comp hf).add_const _

/-- A zero-boundary GFF plus a continuous function remains in GM's class under
the inverse-coordinate pullback, on the original probability space. -/
theorem gm_class_pullback
    (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (h z : Ω → DistOn U) (f : Ω → C(U, ℝ))
    (hz : IsZeroBoundaryGFF U z P) (hf : Measurable f)
    (heq : ∀ᵐ ω ∂P, h ω = z ω +
      Distribution.ofFun U (Function.extend Subtype.val (f ω) 0) volume ⊤) :
    IsZeroBoundaryGFF V
      (fun ω => SupercriticalConformalCovariance.ZBConformal.distPullback (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (z ω)) P ∧
    Measurable (fun ω => gmCorrection Q hφ (f ω)) ∧
    (∀ᵐ ω ∂P,
      confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (h ω) =
        SupercriticalConformalCovariance.ZBConformal.distPullback (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (z ω) +
          Distribution.ofFun V
            (Function.extend Subtype.val (gmCorrection Q hφ (f ω)) 0) volume ⊤) := by
  let ψ := SupercriticalConformalCovariance.Reversal.inverse_conformal hφ
  have hzb := SupercriticalConformalCovariance.ZBConformal.isZeroBoundaryGFF_distPullback ψ hz
  refine ⟨hzb, measurable_gmCorrection Q hφ hf, ?_⟩
  filter_upwards [heq] with ω hω
  have hlog : Distribution.ofFun V (fun y => Q * Real.log ‖deriv (invFunOn φ U) y‖)
      volume ⊤ =
      Distribution.ofFun V
        (Function.extend Subtype.val (SupercriticalConformalCovariance.GPull.logDerivCont Q ψ) 0) volume ⊤ := by
    ext χ
    have hcont := SupercriticalConformalCovariance.GPull.continuousOn_logDeriv Q ψ
    calc
      _ = ∫ y, (Q * Real.log ‖deriv (invFunOn φ U) y‖) * χ y :=
        SupercriticalConformalCovariance.GPull.ofFun_continuousOn_apply hcont χ
      _ = _ := (SupercriticalConformalCovariance.GPull.ofFun_extZ_apply_eq
        (SupercriticalConformalCovariance.GPull.logDerivCont Q ψ) hcont (by intro y hy; rfl) χ).symm
  rw [hω, SupercriticalConformalCovariance.Root.confPullbackField_add, SupercriticalConformalCovariance.Root.precomp_ofFun_extZ]
  change (SupercriticalConformalCovariance.ZBConformal.distPullback ψ (z ω) +
      Distribution.ofFun V (fun y => Q * Real.log ‖deriv (invFunOn φ U) y‖) volume ⊤) +
      Distribution.ofFun V
        (Function.extend Subtype.val ((f ω).comp (SupercriticalConformalCovariance.Root.mapsToCM ψ)) 0) volume ⊤ =
      SupercriticalConformalCovariance.ZBConformal.distPullback ψ (z ω) +
        Distribution.ofFun V
          (Function.extend Subtype.val (gmCorrection Q hφ (f ω)) 0) volume ⊤
  rw [hlog]
  change _ + _ = _ +
    Distribution.ofFun V
      (Function.extend Subtype.val
        ((f ω).comp (SupercriticalConformalCovariance.Root.mapsToCM ψ) + SupercriticalConformalCovariance.GPull.logDerivCont Q ψ) 0) volume ⊤
  erw [SupercriticalConformalCovariance.Domain.ofFun_extZ_add V
    ((f ω).comp (SupercriticalConformalCovariance.Root.mapsToCM ψ)) (SupercriticalConformalCovariance.GPull.logDerivCont Q ψ)]
  ac_rfl

end SupercriticalConformalCovariance.GMForm
