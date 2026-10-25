import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.FV2ScaleIff




 





set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

theorem subtractBumpsV2_add_bumpSum
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ)
    (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) :
    EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z
      (LQGMetric.addFun g
        (LQGMetric.testCont
          (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z))) = g := by
  change LQGMetric.GM.subTest
      (LQGMetric.addFun g
        (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z)))
      (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z) = g
  rw [EndSaving.Choices.subTest_addFun, sub_self]
  exact EndSaving.Choices.addFun_zero g

theorem normalizedFV2_shifted_ae_iff_raw
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (hD : IsWeakLQGMetric ξ Q D)
    (hD' : IsWeakLQGMetric ξ Q D')
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) :
    let φ := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z
    ∀ᵐ ω ∂P,
      EndSaving.NormalizedEvent.NormalizedFV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z
        (LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) ↔
      EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z
        (LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) := by
  dsimp only
  let φ := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z
  filter_upwards [EndSaving.Choices.ae_regularAt_shift hD P h hh φ,
    EndSaving.Choices.ae_regularAt_shift hD' P h hh φ,
    EndSaving.Choices.ae_regularAt_self hD P h hh] with ω hregD hregD' hregH
  let g := LQGMetric.addFun (h ω) (LQGMetric.testCont φ)
  let c := -(EndSaving.NormalizedEvent.unitNorm g)
  have hsub : EndSaving.FiniteEvents.subtractBumpsV2 P h D D' ξ Q cMid par pbar r obj Z g = h ω := by
    exact subtractBumpsV2_add_bumpSum P h D D' ξ Q cMid par pbar r obj Z (h ω)
  have hDscale : ∀ x y : ℂ,
      D (LQGMetric.addConst g c) (x, y) =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) * D g (x, y) := by
    intro x y
    exact metric_addConst_eq_mul_of_regular D (ξ : ℝ) g hregD c (x, y)
  have hD'scale : ∀ x y : ℂ,
      D' (LQGMetric.addConst g c) (x, y) =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) * D' g (x, y) := by
    intro x y
    exact metric_addConst_eq_mul_of_regular D' (ξ : ℝ) g hregD' c (x, y)
  have hSubscale : ∀ x y : ℂ,
      D (LQGMetric.addConst
        (EndSaving.FiniteEvents.subtractBumpsV2 P h D D' ξ Q cMid par pbar r obj Z g) c) (x, y) =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) *
          D (EndSaving.FiniteEvents.subtractBumpsV2 P h D D' ξ Q cMid par pbar r obj Z g) (x, y) := by
    intro x y
    rw [hsub]
    exact metric_addConst_eq_mul_of_regular D (ξ : ℝ) (h ω) hregH c (x, y)
  have hiff := fV2_addConst_iff_of_distance_scale P h D D' ξ Q cMid cPlus
    par pbar r b q K₁ K₂ obj Z g c hDscale hD'scale hSubscale
  simpa only [EndSaving.NormalizedEvent.NormalizedFV2, EndSaving.NormalizedEvent.normalizedField] using hiff

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
