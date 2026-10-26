import SupercriticalConformalCovariance.Small.ZoomGeometry
import SupercriticalConformalCovariance.Small.ZoomWitness
import SupercriticalConformalCovariance.Reversal.Inverse

/-!
# The global-domain zoom realization bridge, as one named hypothesis

`ZoomRealizationBridge` is the exact statement the Proposition 4.3 proof proves as
`SupercriticalConformalCovariance.Small.isDomainRealization_zoom_subConst` (`SupercriticalConformalCovariance.Small.ZoomFieldSquare`):
if `(g, k)` realizes the transformed field `h^φ = h ∘ φ⁻¹ + Q log |(φ⁻¹)′|` on `V`, then for every
scale `(z, r)` and every measurable recentring constant `c`, the corrected pair
`(g ∘ B, k ∘ B − c)` (`B(t) = φ(z) + r t`) realizes the transformed field of the recentred zoom
`h(z + r ·) − c` on the zoomed global domain `B⁻¹(V)`. Paper l. 338–344 ("Affine covariance and
Weyl scaling identify the rescaled source and pullback metrics ..."), with the corrected realization pair
(the zoom identity of l. 345–349 is correct as printed).

`zoomData_realization_of_bridge` packages the bridge as the realization data consumed by
`SupercriticalConformalCovariance.Small.tangent_limit_conf_law_varying` (the bridge version of the Proposition 4.3 proof's
`zoomRealizationData_realization`, which uses the proved bridge directly).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace

namespace SupercriticalConformalCovariance.P43Final

open LQGMetric (DistC restrictTo addConst affineComp affinePt ofCont)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)
open SupercriticalConformalCovariance.Small (affinePreimage zoomConformal affinePreimage_conformal negConstOn)

/-- **The zoom realization bridge** (the one named hypothesis of `prop43Input_of_bridge`). -/
def ZoomRealizationBridge : Prop :=
  ∀ (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ}
    (hr : 0 < r) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h g : Ω → DistC}
    {k : Ω → C(V, ℝ)},
    IsDomainRealization V P
      (fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (restrictTo U (h ω))) g k →
    ∀ (c : Ω → ℝ), Measurable c →
    IsDomainRealization (affinePreimage V (φ z) r) P
      (fun ω => confPullbackField Q
        (SupercriticalConformalCovariance.Reversal.inverse_conformal (zoomConformal hφ z hr))
        (restrictTo (affinePreimage U z r) (addConst (affineComp r z (h ω)) (-(c ω)))))
      (fun ω => affineComp r (φ z) (g ω))
      (fun ω => (k ω).comp (SupercriticalConformalCovariance.Root.mapsToCM (affinePreimage_conformal V (φ z) hr)) +
        negConstOn (affinePreimage V (φ z) r) (c ω))

end SupercriticalConformalCovariance.P43Final
