import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.FbarScaleCore
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.FV2Scale




 




set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

theorem fV2_of_distance_scale
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
    (c : ℝ)
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
          D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g) (x, y))
    (hF : EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z g) :
    EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z (LQGMetric.addConst g c) := by
  let k := Real.exp ((ξ : ℝ) * c)
  have hk : 0 < k := Real.exp_pos _
  rcases hF with ⟨hbar, P, T, hgeo, hstable⟩
  refine ⟨fbarV2_of_distance_scale μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z g c hDscale hD'scale hbar,
    P ∘ fun t => t / k, k * T, ?_, ?_⟩
  · rw [subtractBumpsV2_addConst]
    exact uniqueSetGeodesic_rescale
      (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g))
      (D (LQGMetric.addConst
        (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g) c))
      k hk hSubscale K₁ K₂ P T hgeo
  · intro i hi
    exact stableAtV2_of_distance_scale μ h D D' ξ Q cMid par pbar r obj
      g P T i c hDscale (hstable i hi)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
