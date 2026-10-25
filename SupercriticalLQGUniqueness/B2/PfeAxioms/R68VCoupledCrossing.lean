import SupercriticalLQGUniqueness.B2.Final.CouplingData
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedAcrossConvergence

 






set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem ae_coupled_acrossDist_tendsto
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (A : EuclideanAnnulus) :
    ∀ᵐ ω ∂P',
      Tendsto (fun n => acrossDist
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))) A)
        atTop (𝓝 (acrossDist (L ω) A)) := by
  have hSmall : ∀ᵐ ω ∂P', ∀ k : ℕ,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)))
        (L ω) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)) :=
    ae_all_iff.mpr hSA
  filter_upwards [hB.metric_tendsto, hSmall] with ω hC hS
  have hSphere := PfeWeyl.sphere_setDistance_tendsto_of_lsc hC
    (fun n => PfeWeyl.isLengthSpace_normalizedLFPPMetric
      (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)))
    (fun n => continuous_euclidForget_normalizedLFPPMetric
      (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)))
    hS (c := A.center) (c' := A.center)
    (r := A.innerRadius) (r' := A.outerRadius)
    A.property.1 (A.property.1.trans A.property.2)
  simpa only [acrossDist, setDistance, EuclideanAnnulus.innerBoundary,
    EuclideanAnnulus.outerBoundary] using hSphere

end SupercriticalLQGUniqueness.B2.PfeAxioms
