import SupercriticalConformalCovariance.Small.Normalization
import SupercriticalLQGUniqueness.B2.Strong.Scale

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open LQGMetric
open SupercriticalLQGUniqueness

/-- Affine covariance and Weyl scaling for a smoothly recentered source field.
The random centering may be any real-valued measurable function. -/
theorem ae_rescaled_source_metric
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P)
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      D (addConst (affineComp (r : ℝ) z (h ω)) (-c ω)) (u,v) =
        ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
          Real.exp (-((ξ : ℝ) * c ω))) *
          D (h ω) (z + (r : ℂ) * u, z + (r : ℂ) * v) := by
  let ht : Ω → DistC := fun ω =>
    addConst (affineComp (r : ℝ) z (h ω)) (Q * Real.log (r : ℝ))
  have hht : IsGFFPlusCont ht P :=
    Uniqueness.Toolkit.LocalEvents.isGFFPlusCont_addConst
      (LQGMetric.GM.isGFFPlusCont_affineComp hh r.2 z) measurable_const
  filter_upwards [hD.2.2.2.2.1 P h hh r z,
    hD.2.2.2.1 P ht hht, hD.2.1 P ht hht] with ω hcoord hweyl hlen
  intro u v
  let a : ℝ := -(Q * Real.log (r : ℝ)) - c ω
  have hfield : addConst (affineComp (r : ℝ) z (h ω)) (-c ω) =
      addFun (ht ω) (ContinuousMap.const ℂ a) := by
    dsimp [ht]
    rw [B2.Strong.addFun_addConst_const]
    congr 1
    dsimp [a]
    ring
  have hw := congrFun (hweyl (ContinuousMap.const ℂ a)) (u,v)
  rw [weylScale_const _ _ _ hlen] at hw
  rw [hfield, ← hw]
  have he : Real.exp ((ξ : ℝ) * a) =
      (r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * c ω)) := by
    exact SupercriticalLQGUniqueness.B2.Strong.exp_scale_eq
      (ξ : ℝ) Q (r : ℝ) (c ω) r.2
  rw [he]
  have hc := hcoord u v
  have hc' : D (ht ω) (u,v) =
      D (h ω) (z + (r : ℂ) * u, z + (r : ℂ) * v) := by
    simpa only [ht, B2.Strong.scaleTranslateDist_eq_affineComp,
      Complex.real_smul, add_comm] using hc.symm
  rw [hc']

end SupercriticalConformalCovariance.Small
