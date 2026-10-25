import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Circles
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteLimit

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_acrossDist_tendsto_of_smallAnnulusCosts
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (A : EuclideanAnnulus) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => acrossDist
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω)) A)
        atTop (𝓝 (acrossDist (D (h ω)) A)) := by
  have hConv := ae_normalizedLFPPMetric_tendsto ξ m ε D hD P h hh X hX
  have hSmall : ∀ᵐ ω ∂P, ∀ k : ℕ,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)) :=
    ae_all_iff.mpr hsmall
  filter_upwards [hConv, hSmall] with ω hC hS
  have hSphere := PfeWeyl.sphere_setDistance_tendsto_of_lsc hC
    (fun n => PfeWeyl.isLengthSpace_normalizedLFPPMetric
      (ξ : ℝ) (m (ε n)) (X (ε n) ω))
    (fun n => continuous_euclidForget_normalizedLFPPMetric
      (ξ : ℝ) (m (ε n)) (X (ε n) ω))
    hS (c := A.center) (c' := A.center)
    (r := A.innerRadius) (r' := A.outerRadius)
    A.property.1 (A.property.1.trans A.property.2)
  simpa only [acrossDist, setDistance, EuclideanAnnulus.innerBoundary,
    EuclideanAnnulus.outerBoundary] using hSphere

end SupercriticalLQGUniqueness.B2.PfeAxioms
