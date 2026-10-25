import SupercriticalLQGUniqueness.B2.Median.NoGap
import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsGeometry0

 








set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

 

theorem noGap_crossingInf_finite_of_limitEuclideanControl0
    (hInput : PfeAxioms.Inputs.LimitEuclideanControl0)
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : LQGMetric.DistC → LSCMetric)
    (hD : B2.Iface.SubseqLimit ξ m ε D)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (x y : ℝ≥0∞) (hxy : x < y) (hyfin : y ≠ ∞)
    (hpos : 0 < P {ω | crossingInf (D (h ω)) ≤ x}) :
    0 < P {ω | x < crossingInf (D (h ω)) ∧ crossingInf (D (h ω)) < y} :=
  noGap_crossingInf_finite_of_ae_euclideanForget ξ D c hweak P h hh
    (PfeAxioms.Inputs.ae_euclideanForget_continuous_of_inputs0_existsExponent
      hInput ξ m ε D hm hε hD P h hh)
    x y hxy hyfin hpos

end SupercriticalLQGUniqueness.B2.Median
