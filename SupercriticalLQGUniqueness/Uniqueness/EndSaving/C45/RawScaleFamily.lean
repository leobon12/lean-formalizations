import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.FV2UniformBudget
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.CountWitness




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
open LQGMetric (DistC)

theorem raw_scale_borel_family
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (k : ℕ) (B : ℝ≥0∞)
    (hbudget : (∑' Z : Finset (ℤ × ℤ),
      P {ω | EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
        EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
          r b q K₁ K₂ obj Z (h ω)}) ≤ B) :
    ∃ A : Finset (ℤ × ℤ) → Set Ω,
      (∀ Z, MeasurableSet (A Z)) ∧
      (∀ᵐ ω ∂P, ∀ Z, (ω ∈ A Z) ↔
        (EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
          EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
            r b q K₁ K₂ obj Z (h ω))) ∧
      (∑' Z, P (A Z)) ≤ B := by
  classical
  let eligible (Z : Finset (ℤ × ℤ)) :=
    EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k
  let proxy (Z : Finset (ℤ × ℤ)) : Set DistC :=
    Classical.choose (raw_fV2_borel_proxy P h hh D D' ξ Q cMid cPlus
      hD hD' par pbar r b q K₁ K₂ hK₁ hK₂ obj Z)
  have hp (Z : Finset (ℤ × ℤ)) :=
    Classical.choose_spec (raw_fV2_borel_proxy P h hh D D' ξ Q cMid cPlus
      hD hD' par pbar r b q K₁ K₂ hK₁ hK₂ obj Z)
  let A (Z : Finset (ℤ × ℤ)) : Set Ω :=
    {ω | eligible Z ∧ h ω ∈ proxy Z}
  have hA : ∀ Z, MeasurableSet (A Z) := by
    intro Z
    have he : MeasurableSet {ω : Ω | eligible Z} := by
      by_cases hz : eligible Z <;> simp [hz]
    exact he.inter ((hp Z).1.preimage hh.1.measurable)
  have heqAll : ∀ᵐ ω ∂P, ∀ Z : Finset (ℤ × ℤ),
      (ω ∈ A Z) ↔
        (EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
          EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
            r b q K₁ K₂ obj Z (h ω)) := by
    apply ae_all_iff.mpr
    intro Z
    have heq := ae_of_ae_map hh.1.measurable.aemeasurable (hp Z).2.2.2.1
    filter_upwards [heq, EndSaving.NormalizedEvent.normalizedFV2_ae_iff_raw P h hh
      D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z] with ω he hr
    simp only [A, Set.mem_ofPred_eq, eligible]
    constructor
    · rintro ⟨⟨hc, hk⟩, hp⟩
      exact ⟨hc, hk, ((Iff.of_eq he).symm.trans hr).mp hp⟩
    · rintro ⟨hc, hk, hf⟩
      exact ⟨⟨hc, hk⟩, ((Iff.of_eq he).symm.trans hr).mpr hf⟩
  have hmeasure (Z : Finset (ℤ × ℤ)) :
      P (A Z) = P {ω | EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
        EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
          r b q K₁ K₂ obj Z (h ω)} := by
    apply measure_congr
    filter_upwards [heqAll] with ω he
    exact propext (he Z)
  refine ⟨A, hA, heqAll, ?_⟩
  simpa only [hmeasure] using hbudget

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
