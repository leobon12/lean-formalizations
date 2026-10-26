import SupercriticalConformalCovariance.Frozen.ConfPullbackField
import SupercriticalConformalCovariance.Frozen.IsDomainRealization
import LQGMetric.Field.Measurable

set_option autoImplicit false
noncomputable section

open MeasureTheory TopologicalSpace
open LQGMetric (DistOn TestOn measurable_distOn_iff measurable_distOn_apply)

namespace SupercriticalConformalCovariance.GPull

open SupercriticalConformalCovariance

/-- The candidate conformal pullback is measurable for the cylinder sigma algebras. -/
theorem measurable_confPullbackField (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) :
    Measurable (confPullbackField Q hφ) := by
  apply measurable_distOn_iff.mpr
  intro ψ
  exact (measurable_distOn_apply (confPushTest hφ ψ)).add_const _

/-- Every domain realization gives a measurable pulled-back field on its original space. -/
theorem measurable_pullback_of_realization
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V)
    {h : Ω → DistOn V} {h₀ : Ω → LQGMetric.DistC} {f : Ω → C(V, ℝ)}
    (hr : IsDomainRealization V P h h₀ f) :
    Measurable (fun ω => confPullbackField Q hφ (h ω)) :=
  (measurable_confPullbackField Q hφ).comp hr.1

/-- The same measurability survives every measure-preserving extension. -/
theorem measurable_pullback_on_extension
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V)
    {h : Ω → DistOn V} {h₀ : Ω → LQGMetric.DistC} {f : Ω → C(V, ℝ)}
    (hr : IsDomainRealization V P h h₀ f)
    (π : Ω' → Ω) (hπ : MeasurePreserving π P' P) :
    Measurable (fun ω' => confPullbackField Q hφ (h (π ω'))) :=
  (measurable_pullback_of_realization P Q hφ hr).comp hπ.measurable

/-- A domain realization exposes its whole-plane GFF core and global continuous correction. -/
theorem exists_whole_plane_core
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (V : Opens ℂ)
    {h : Ω → DistOn V} {h₀ : Ω → LQGMetric.DistC} {f : Ω → C(V, ℝ)}
    (hr : IsDomainRealization V P h h₀ f) :
    ∃ c : Ω → C(ℂ, ℝ), Measurable c ∧
      LQGMetric.IsWholePlaneGFF (fun ω => h₀ ω - LQGMetric.ofCont (c ω)) P :=
  hr.2.1.2


end SupercriticalConformalCovariance.GPull
