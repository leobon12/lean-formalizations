import SupercriticalConformalCovariance.Frozen.ConformalCovariance
import SupercriticalConformalCovariance.Reversal.Field
import SupercriticalConformalCovariance.Frozen.XiCrit
import SupercriticalConformalCovariance.Frozen.IsGreenian
import SupercriticalConformalCovariance.Frozen.IsDomainRealization
import SupercriticalConformalCovariance.Frozen.DomainMetric
import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric

set_option autoImplicit false
noncomputable section

open MeasureTheory TopologicalSpace Set Function
open LQGMetric (DistC DistOn)
open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GMForm

/-- The forward GM direction follows from the frozen conformal-covariance theorem. -/
theorem gm_direction_of_root
    (ξ : Set.Ioi (0 : ℝ)) (hξ : xiCrit < (ξ : ℝ))
    (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U V : Opens ℂ) (hUc : IsConnected (U : Set ℂ)) (hVc : IsConnected (V : Set ℂ))
    (hUg : IsGreenian U) (hVg : IsGreenian V)
    (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn U) (h₀ : Ω → DistC) (f : Ω → C(U, ℝ))
    (hr : IsDomainRealization U P h h₀ f) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
        (g₀ : Ω' → DistC) (k : Ω' → C(V, ℝ)), MeasurePreserving π P' P ∧
      IsDomainRealization V P'
        (fun ω' => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (h (π ω')))
        g₀ k) ∧
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (π : Ω' → Ω),
      MeasurePreserving π P' P →
      ∀ (g₀ : Ω' → DistC) (k : Ω' → C(V, ℝ)),
        IsDomainRealization V P'
          (fun ω' => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (h (π ω')))
          g₀ k →
        ∀ᵐ ω' ∂P', ∀ z w : U,
          domainMetric (ξ : ℝ) D U (h₀ (π ω')) (f (π ω')) (z, w) =
            domainMetric (ξ : ℝ) D V (g₀ ω') (k ω')
              (⟨φ z, hφ.2.mapsTo z.2⟩, ⟨φ w, hφ.2.mapsTo w.2⟩) := by
  let ψ := SupercriticalConformalCovariance.Reversal.inverse_conformal hφ
  have hh := SupercriticalConformalCovariance.conformal_covariance ξ hξ Q hQ D hD V U hVc hUc hVg hUg (invFunOn φ U) ψ
    P h h₀ f hr
  refine ⟨hh.1, ?_⟩
  intro Ω' _ P' π hπ g₀ k hreal
  have he := hh.2 Ω' P' π hπ g₀ k hreal
  filter_upwards [he] with ω hω
  intro z w
  have hz : invFunOn φ U (φ z) = z :=
    hφ.2.injOn.leftInvOn_invFunOn z.2
  have hw : invFunOn φ U (φ w) = w :=
    hφ.2.injOn.leftInvOn_invFunOn w.2
  simpa only [Subtype.ext_iff, hz, hw] using
    hω (⟨φ z, hφ.2.mapsTo z.2⟩) (⟨φ w, hφ.2.mapsTo w.2⟩)

end SupercriticalConformalCovariance.GMForm
