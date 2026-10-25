import SupercriticalLQGUniqueness.B2.PfeAxioms.Section4AnnulusFinite0
import SupercriticalLQGUniqueness.B2.PfeAxioms.LimitAEMeasurableNormalized
import SupercriticalLQGUniqueness.B2.PfeAxioms.FixedTightness
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem twoSidedTight_fixed_annulus_of_section4
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (A : EuclideanAnnulus) :
    IsTwoSidedTight P (fun (_ : ℕ) ω => acrossDist (D (h ω)) A) ∧
    IsTwoSidedTight P (fun (_ : ℕ) ω => aroundDist (D (h ω)) A) := by
  have hDm := aemeasurable_limit_metric_normalized ξ m ε D hD P h hh X hX
  have hcost := ae_annulus_costs_pos_finite_of_section4
    hS ξ Q hQ m hm ε hε D hD P h hh X hX A
  constructor
  · apply isTwoSidedTight_const_of_ae_pos_finite P
      (fun ω => acrossDist (D (h ω)) A)
      ((measurable_acrossDist A).comp_aemeasurable hDm)
    · exact hcost.mono fun _ hω => hω.1
    · exact hcost.mono fun _ hω => hω.2.1
  · apply isTwoSidedTight_const_of_ae_pos_finite P
      (fun ω => aroundDist (D (h ω)) A)
      ((Uniqueness.TwoScale.S36.measurable_aroundDist_fixed A).comp_aemeasurable hDm)
    · exact hcost.mono fun _ hω => hω.2.2.1
    · exact hcost.mono fun _ hω => hω.2.2.2

end SupercriticalLQGUniqueness.B2.PfeAxioms
