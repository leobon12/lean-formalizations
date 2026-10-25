import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.ScaleInverse




 


set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

theorem fV2_addConst_iff_of_distance_scale
    {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) (c : ℝ)
    (hDscale : ∀ x y : ℂ,
      D (LQGMetric.addConst g c) (x, y) =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) * D g (x, y))
    (hD'scale : ∀ x y : ℂ,
      D' (LQGMetric.addConst g c) (x, y) =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) * D' g (x, y))
    (hSubscale : ∀ x y : ℂ,
      D (LQGMetric.addConst
        (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g) c) (x, y) =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) *
          D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g) (x, y)) :
    EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z (LQGMetric.addConst g c) ↔
    EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z g := by
  constructor
  · intro hF
    have hDinv := inverse_metric_addConst_scale D (ξ : ℝ) g c hDscale
    have hD'inv := inverse_metric_addConst_scale D' (ξ : ℝ) g c hD'scale
    have hSubInv : ∀ x y : ℂ,
        D (LQGMetric.addConst
          (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z
            (LQGMetric.addConst g c)) (-c)) (x, y) =
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * -c)) *
            D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z
              (LQGMetric.addConst g c)) (x, y) := by
      simpa only [subtractBumpsV2_addConst] using
        inverse_metric_addConst_scale D (ξ : ℝ)
          (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g)
          c hSubscale
    have hback := fV2_of_distance_scale μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z (LQGMetric.addConst g c) (-c)
      hDinv hD'inv hSubInv hF
    simpa only [LQGMetric.GFFLaw.addConst_addConst, add_neg_cancel,
      LQGMetric.GFFLaw.addConst_zero'] using hback
  · exact fV2_of_distance_scale μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z g c hDscale hD'scale hSubscale

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
