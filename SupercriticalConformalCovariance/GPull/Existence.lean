import SupercriticalConformalCovariance.GPull.Identity
import SupercriticalConformalCovariance.GPull.GreenianMarkov

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set
open LQGMetric SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GPull

/-- The existence conjunct of the revision 2.2 root candidate, for Greenian domains. -/
theorem exists_confPullback_domainRealization_greenian
    (U V : Opens ℂ) (hU : IsGreenian U) (hV : IsGreenian V)
    (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ) (h : Ω → DistOn V) (h₀ : Ω → DistC) (f : Ω → C(V, ℝ))
    (hr : IsDomainRealization V P h h₀ f) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
        (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
      MeasurePreserving π P' P ∧
      IsDomainRealization U P'
        (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k := by
  obtain ⟨c, hcm, hw⟩ := exists_whole_plane_core P V hr
  let w : Ω → DistC := fun ω => h₀ ω - ofCont (c ω)
  obtain ⟨FV, HV, hFVm, _, hzU, hHVm, hHVc, hVpair⟩ :=
    exists_greenian_pullback_markov hw hφ hV
  let z : Ω → DistOn U := fun ω =>
    SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V (FV (w ω)))
  obtain ⟨P', FU, HU, hP', hfst, hg, hFUm, hHUm, hHUc, hzeq, hUpair⟩ :=
    exists_reference_coupling P hzU hU
  obtain ⟨k, hkm, hkpair⟩ :=
    exists_measurable_correction hφ Q hfst hHVm hHVc hHUm hHUc hcm hr.2.2.1
  let g₀ : (Ω × DistC) → DistC := Prod.snd
  have hgpc : IsGFFPlusCont g₀ P' := by
    exact LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hg
  have hreal : ∀ᵐ p ∂P',
      confPullbackField Q hφ (h p.1) =
        restrictTo U (g₀ p) +
          Distribution.ofFun U (Function.extend Subtype.val (k p) 0) volume ⊤ := by
    have hhr : ∀ᵐ p ∂P',
        h p.1 = restrictTo V (h₀ p.1) +
          Distribution.ofFun V (Function.extend Subtype.val (f p.1) 0) volume ⊤ := by
      have h' : ∀ᵐ ω ∂P'.map (Prod.fst : Ω × DistC → Ω),
          h ω = restrictTo V (h₀ ω) +
            Distribution.ofFun V (Function.extend Subtype.val (f ω) 0) volume ⊤ := by
        simpa only [hfst.map_eq] using hr.2.2.2
      exact ae_of_ae_map measurable_fst.aemeasurable h'
    have hVp : ∀ᵐ p ∂P', ∀ ψ : TestOn U,
        (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V (w p.1)) -
          SupercriticalConformalCovariance.ZBConformal.distPullback hφ
            (restrictTo V (FV (w p.1)))) ψ =
          ∫ x, HV p.1 (φ x) * ψ x := by
      have h' : ∀ᵐ ω ∂P'.map (Prod.fst : Ω × DistC → Ω), ∀ ψ : TestOn U,
          (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V (w ω)) -
            SupercriticalConformalCovariance.ZBConformal.distPullback hφ
              (restrictTo V (FV (w ω)))) ψ =
            ∫ x, HV ω (φ x) * ψ x := by
        simpa only [hfst.map_eq] using hVpair
      exact ae_of_ae_map measurable_fst.aemeasurable h'
    have hHVc' : ∀ᵐ p ∂P',
        Continuous fun x : U => HV p.1 (φ x) := by
      have h' : ∀ᵐ ω ∂P'.map (Prod.fst : Ω × DistC → Ω),
          Continuous fun x : U => HV ω (φ x) := by
        simpa only [hfst.map_eq] using hHVc
      exact ae_of_ae_map measurable_fst.aemeasurable h'
    filter_upwards [hhr, hHVc', hVp, hHUc, hzeq, hUpair, hkpair] with
      p hp hcV hpV hcU heq hpU hk
    have hw' : h₀ p.1 = w p.1 + ofCont (c p.1) := by
      dsimp [w]
      abel
    exact pullback_realization_identity hφ Q (h p.1) (h₀ p.1) (w p.1)
      p.2 (FV (w p.1)) (FU p.2) (c p.1) (f p.1) (k p)
      (HV p.1) (HU p.2) hp hw' hcV hcU hpV hpU heq hk
  refine ⟨Ω × DistC, inferInstance, P', Prod.fst, g₀, k, hfst, ?_⟩
  exact ⟨measurable_pullback_on_extension P P' Q hφ hr Prod.fst hfst,
    hgpc, hkm, hreal⟩


end SupercriticalConformalCovariance.GPull
