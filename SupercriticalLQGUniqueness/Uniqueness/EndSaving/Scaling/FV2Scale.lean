import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.FbarScale




 





set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

theorem subtractBumpsV2_addConst
    {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ)
    (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) (c : ℝ) :
    EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z
      (LQGMetric.addConst g c) =
    LQGMetric.addConst
      (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g) c := by
  unfold EndSaving.FiniteEvents.subtractBumpsV2 LQGMetric.GM.subTest LQGMetric.addConst LQGMetric.addFun
  abel

theorem fV2_addConst_of_regular
    {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC)
    (hregD : EndSaving.Choices.RegularAt D (ξ : ℝ) g)
    (hregD' : EndSaving.Choices.RegularAt D' (ξ : ℝ) g)
    (hregSub : EndSaving.Choices.RegularAt D (ξ : ℝ)
      (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g))
    (c : ℝ)
    (hF : EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z g) :
    EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z (LQGMetric.addConst g c) := by
  let k := Real.exp ((ξ : ℝ) * c)
  have hk : 0 < k := Real.exp_pos _
  rcases hF with ⟨hbar, P, T, hgeo, hstable⟩
  have hSubscale : ∀ x y : ℂ,
      D (LQGMetric.addConst
        (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g) c) (x, y) =
        ENNReal.ofReal k *
          D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g) (x, y) := by
    intro x y
    exact metric_addConst_eq_mul_of_regular D (ξ : ℝ) _ hregSub c (x, y)
  refine ⟨fbarV2_addConst μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z g hregD hregD' c hbar,
    P ∘ fun t => t / k, k * T, ?_, ?_⟩
  · rw [subtractBumpsV2_addConst]
    exact uniqueSetGeodesic_rescale
      (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g))
      (D (LQGMetric.addConst
        (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g) c))
      k hk hSubscale K₁ K₂ P T hgeo
  · intro i hi
    exact stableAtV2_addConst μ h D D' ξ Q cMid par pbar r obj
      g hregD P T i c (hstable i hi)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
