import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.SizeBinScale




 


set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

theorem stableAtV2_addConst
    {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ)
    (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (g : DistC) (hreg : EndSaving.Choices.RegularAt D (ξ : ℝ) g)
    (P : ℝ → ℂ) (T : ℝ) (i : ℤ × ℤ) (c : ℝ)
    (hstable : EndSaving.FiniteEvents.StableAtV2 μ h D D' ξ Q cMid par pbar r obj
      g P T i) :
    EndSaving.FiniteEvents.StableAtV2 μ h D D' ξ Q cMid par pbar r obj
      (LQGMetric.addConst g c)
      (P ∘ fun t => t / Real.exp ((ξ : ℝ) * c))
      (Real.exp ((ξ : ℝ) * c) * T) i := by
  let k := Real.exp ((ξ : ℝ) * c)
  have hk : 0 < k := Real.exp_pos _
  let z := LQGMetric.GM.gridPt ((r : ℝ) / 100) i
  let W := Metric.ball z (4 * (r : ℝ))
  rcases hstable with ⟨a, ha, τ', τ, σ, σ', hex, hτ, hσ, hbound⟩
  have htime (s : ℝ) : (k * s) / k = s := by field_simp
  have hτ' : (P ∘ fun t => t / Real.exp ((ξ : ℝ) * c)) (k * τ) ∈ W := by
    change P ((k * τ) / k) ∈ W
    rw [htime]
    exact hτ
  have hσ' : (P ∘ fun t => t / Real.exp ((ξ : ℝ) * c)) (k * σ) ∈ W := by
    change P ((k * σ) / k) ∈ W
    rw [htime]
    exact hσ
  refine ⟨a + c, isCircleAverage_addConst g r z a c ha,
    k * τ', k * τ, k * σ, k * σ',
    excursion_rescale P T W (obj i).V τ' τ σ σ' k hk hex,
    hτ', hσ', ?_⟩
  · have hargτ : (P ∘ fun t => t / Real.exp ((ξ : ℝ) * c)) (k * τ) = P τ := by
      change P ((k * τ) / k) = P τ
      rw [htime]
    have hargσ : (P ∘ fun t => t / Real.exp ((ξ : ℝ) * c)) (k * σ) = P σ := by
      change P ((k * σ) / k) = P σ
      rw [htime]
    have hptτ : (⟨_, hτ'⟩ : W) = ⟨P τ, hτ⟩ := Subtype.ext hargτ
    have hptσ : (⟨_, hσ'⟩ : W) = ⟨P σ, hσ⟩ := Subtype.ext hargσ
    rw [hptτ, hptσ]
    change ENNReal.ofReal par.Ctime *
        ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * (a + c))) ≤
      (D (LQGMetric.addConst g c)).internal W
        (⟨P τ, hτ⟩, ⟨P σ, hσ⟩)
    calc
      _ = ENNReal.ofReal k *
          (ENNReal.ofReal par.Ctime *
            ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) *
              Real.exp ((ξ : ℝ) * a))) := by
            rw [normalizer_addConst]
            ring
      _ ≤ ENNReal.ofReal k * (D g).internal W
          (⟨P τ, hτ⟩, ⟨P σ, hσ⟩) := by gcongr
      _ = _ := (internal_addConst_eq_mul_of_regular D (ξ : ℝ) g hreg c W
        (⟨P τ, hτ⟩, ⟨P σ, hσ⟩)).symm

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
