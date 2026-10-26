import SupercriticalConformalCovariance.GPull.Product
import SupercriticalConformalCovariance.GPull.Greenian
import SupercriticalConformalCovariance.Markov.MarkovTheorem
import SupercriticalConformalCovariance.ZBConformal.GFFLaw
import LQGMetric.Complex.HarmonicComp

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set
open LQGMetric SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GPull

/-- The new arbitrary-Greenian Markov theorem transported to the source domain.
The zero-boundary part here is a field on `U`; a canonical whole-plane extension
of this *particular coupled field* is still needed for replacement. -/
theorem exists_greenian_pullback_markov
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {w : Ω → DistC} (hw : IsWholePlaneGFF w P)
    {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (hV : IsGreenian V) :
    ∃ (F : DistC → DistC) (H : Ω → ℂ → ℝ),
      Measurable F ∧
      LQGMetric.CONF.IsZBExtField V (fun ω => F (w ω)) P ∧
      IsZeroBoundaryGFF U
        (fun ω => SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V (F (w ω)))) P ∧
      Measurable (fun p : Ω × U => H p.1 (φ p.2)) ∧
      (∀ᵐ ω ∂P, Continuous fun x : U => H ω (φ x)) ∧
      (∀ᵐ ω ∂P, ∀ ψ : TestOn U,
        (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V (w ω)) -
          SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V (F (w ω)))) ψ =
          ∫ x, H ω (φ x) * ψ x) := by
  obtain ⟨F, H, hFm, _, _, hzbV, hExt, hHm, hHpair, _⟩ :=
    SupercriticalConformalCovariance.Markov.exists_generated_joint_markov_general hw hV
  have hzbU := SupercriticalConformalCovariance.ZBConformal.isZeroBoundaryGFF_distPullback hφ hzbV
  have hφm : Measurable (fun x : U => φ x) :=
    (continuousOn_iff_continuous_domRestrict.mp hφ.1.continuousOn).measurable
  have hpullm : Measurable (fun p : Ω × U => H p.1 (φ p.2)) :=
    hHm.comp (Measurable.prodMk measurable_fst (hφm.comp measurable_snd))
  have hpullc : ∀ᵐ ω ∂P, Continuous fun x : U => H ω (φ x) := by
    filter_upwards [hHpair] with ω hω
    apply continuousOn_univ.mp
    exact hω.1.continuousOn.comp
      (continuousOn_iff_continuous_domRestrict.mp hφ.1.continuousOn).continuousOn
      (fun x _ => hφ.2.mapsTo x.property)
  refine ⟨F, H, hFm, hExt, hzbU, hpullm, hpullc, ?_⟩
  filter_upwards [hHpair] with ω hω
  intro ψ
  have hp := hω.2 (confPushTest hφ ψ)
  rw [sub_apply, SupercriticalConformalCovariance.ZBConformal.distPullback_apply,
    SupercriticalConformalCovariance.ZBConformal.distPullback_apply]
  change (restrictTo V (w ω - F (w ω))) (confPushTest hφ ψ) = _
  rw [hp]
  exact SupercriticalConformalCovariance.ZBConformal.integral_mul_confPushTest hφ ψ (H ω)


end SupercriticalConformalCovariance.GPull
