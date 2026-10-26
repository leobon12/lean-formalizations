import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import SupercriticalConformalCovariance.Frozen.XiCrit
import SupercriticalConformalCovariance.Frozen.IsGreenian
import SupercriticalConformalCovariance.Frozen.ConfPullbackField
import SupercriticalConformalCovariance.Frozen.IsDomainRealization
import SupercriticalConformalCovariance.Frozen.DomainMetric
import SupercriticalConformalCovariance.Root.LocalDischarge
import SupercriticalConformalCovariance.P43Final.Closed

/-!
Provider module of the frozen anchor `SupercriticalConformalCovariance.Frozen.ConformalCovariance` (`SupercriticalConformalCovariance.conformal_covariance`).
The statement and the `open` lines are copied verbatim from the frozen file. The proof is `SupercriticalConformalCovariance.Root.conformal_covariance_of_prop43 SupercriticalConformalCovariance.P43Final.prop43_input_slot` (modules `SupercriticalConformalCovariance.Root.LocalDischarge`, `SupercriticalConformalCovariance.P43Final.Closed`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal
open LQGMetric (DistC DistOn)

namespace SupercriticalConformalCovariance.Implementation

open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)

/-- Provider of `SupercriticalConformalCovariance.conformal_covariance`. -/
theorem conformal_covariance_impl :
    ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
      ∀ U V : Opens ℂ, IsConnected (U : Set ℂ) → IsConnected (V : Set ℂ) →
      IsGreenian U → IsGreenian V →
      ∀ (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V),
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn V) (h₀ : Ω → DistC) (f : Ω → C(V, ℝ)),
        IsDomainRealization V P h h₀ f →
        (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
            (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)), MeasurePreserving π P' P ∧
          IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k) ∧
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (π : Ω' → Ω), MeasurePreserving π P' P →
          ∀ (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
            IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k →
            ∀ᵐ ω' ∂P', ∀ u v : U,
              domainMetric (ξ : ℝ) D V (h₀ (π ω')) (f (π ω'))
                  (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) =
                domainMetric (ξ : ℝ) D U (g₀ ω') (k ω') (u, v) :=
  SupercriticalConformalCovariance.Root.conformal_covariance_of_prop43 SupercriticalConformalCovariance.P43Final.prop43_input_slot

end SupercriticalConformalCovariance.Implementation
