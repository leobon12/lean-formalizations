import SupercriticalLQGUniqueness.B2.Median.UpperBound

 




set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

 


theorem ae_crossing_le_liminf_of_subseqLimit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (D : LQGMetric.DistC → LSCMetric)
    (hsub : B2.Iface.SubseqLimit ξ m ε D)
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsGFFPlusBddCont h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    ∀ᵐ ω ∂P, crossingInf (D (h ω)) ≤
      liminf (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
        lfppCrossingLength (ξ : ℝ) (X (ε n) ω)) atTop := by
  have hlim := (hsub P h hh X hX).1
  filter_upwards [hlim] with ω hω
  exact crossing_le_liminf (ξ : ℝ) (fun n => m (ε n))
    (fun n => X (ε n) ω) (D (h ω)) hω

end SupercriticalLQGUniqueness.B2.Median
