import SupercriticalConformalCovariance.P43Final.Final
import SupercriticalConformalCovariance.Small.ZoomFieldSquare
import SupercriticalConformalCovariance.Root.Assembly

/-!
# Proposition 4.3, closed by the zoom realization bridge

`zoomRealizationBridge_proved`: `SupercriticalConformalCovariance.Small.isDomainRealization_zoom_subConst` is exactly
`ZoomRealizationBridge`. Composed with `prop43Input_of_bridge` it discharges the `hP43` input of
`SupercriticalConformalCovariance.Root.conformal_covariance_of_inputs` (`prop43_input_slot`).
-/

set_option autoImplicit false

namespace SupercriticalConformalCovariance.P43Final

open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsLFPPExponent)

/-- The proved zoom realization bridge is the named hypothesis. -/
theorem zoomRealizationBridge_proved : ZoomRealizationBridge :=
  fun Q _ _ _ hφ z _ hr _ _ _ _ _ _ hR c hc =>
    SupercriticalConformalCovariance.Small.isDomainRealization_zoom_subConst Q hφ z hr hR c hc

/-- **Proposition 4.3** (`SupercriticalConformalCovariance.Root.Prop43Input`), with no hypothesis beyond the setting. -/
theorem prop43Input_proved (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D) : SupercriticalConformalCovariance.Root.Prop43Input ξ Q D :=
  prop43Input_of_bridge zoomRealizationBridge_proved ξ Q hQ D hD

/-- The `hP43` slot of `SupercriticalConformalCovariance.Root.conformal_covariance_of_inputs`, in its exact form. -/
theorem prop43_input_slot :
    ∀ ξ : Set.Ioi (0 : ℝ), SupercriticalConformalCovariance.xiCrit < (ξ : ℝ) → ∀ Q : ℝ,
      IsLFPPExponent ξ Q → ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
        SupercriticalConformalCovariance.Root.Prop43Input ξ Q D :=
  fun ξ _ Q hQ D hD => prop43Input_proved ξ Q hQ D hD

end SupercriticalConformalCovariance.P43Final
