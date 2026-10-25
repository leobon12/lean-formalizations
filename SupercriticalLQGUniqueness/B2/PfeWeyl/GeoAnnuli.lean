import SupercriticalLQGUniqueness.B2.PfeWeyl.AnnulusProbability
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf

 




set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
def innerAnnulus (r : ℝ) (hr : 0 < r) : EuclideanAnnulus :=
  ⟨((0 : ℂ), (r, 2 * r)), hr, by linarith⟩

 
def outerAnnulus (r : ℝ) (hr : 0 < r)
    (R : Set.Ioi (2 * r)) : EuclideanAnnulus :=
  ⟨((0 : ℂ), (2 * r, (R : ℝ))), by linarith, R.property⟩

 


def GeoAnnulusInput {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → LSCMetric) (r : ℝ) (hr : 0 < r) : Prop :=
  AnnulusTailInput P
    (fun ω => aroundDist (D ω) (innerAnnulus r hr))
    (fun (R : Set.Ioi (2 * r)) ω => acrossDist (D ω) (outerAnnulus r hr R))

 

theorem geo_annuli_of_annulusInput
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : Ω → LSCMetric)
    (r : ℝ) (hr : 0 < r)
    (hD : Measurable D)
    (hinput : GeoAnnulusInput P D r hr)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun R : Set.Ioi (2 * r) =>
      P {ω | ENNReal.ofReal C + aroundDist (D ω) (innerAnnulus r hr) <
        (ENNReal.ofReal C)⁻¹ * acrossDist (D ω) (outerAnnulus r hr R)})
      atTop (𝓝 1) := by
  have hc0 : ENNReal.ofReal C ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hC).ne'
  exact geo_annuli_prob_of_annulusInput P
    (fun ω => aroundDist (D ω) (innerAnnulus r hr))
    (fun (R : Set.Ioi (2 * r)) ω =>
      acrossDist (D ω) (outerAnnulus r hr R))
    (Uniqueness.TwoScale.S36.measurable_aroundDist_fixed _ |>.comp hD)
    (fun R => (Uniqueness.Toolkit.PathInfimum.measurable_acrossDist _).comp hD)
    hinput hc0 ENNReal.ofReal_ne_top

end SupercriticalLQGUniqueness.B2.PfeWeyl
