import SupercriticalLQGUniqueness.Uniqueness.EndSaving.NormalizedEvent.NormalizedFV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym.ObjectRNBridgeV2




 






set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem normalized_fV2_probability_window_of_raw_measurable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ))
    (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z)
    (hraw_measurable : MeasurableSet
      {g : DistC | EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z g}) :
    let E : Set DistC :=
      {g | EndSaving.NormalizedEvent.NormalizedFV2 P h D D' ξ Q cMid cPlus par pbar
        r b q K₁ K₂ obj Z g}
    ENNReal.ofReal ((par.Crn⁻¹) ^ Z.card) * P (sampleEvent h E) ≤
      P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
        (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z))) E) ∧
    P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
        (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z))) E) ≤
      ENNReal.ofReal (par.Crn ^ Z.card) * P (sampleEvent h E) := by
  let E : Set DistC := {g | EndSaving.NormalizedEvent.NormalizedFV2 P h D D' ξ Q cMid cPlus
    par pbar r b q K₁ K₂ obj Z g}
  have hE : MeasurableSet E := by
    exact hraw_measurable.preimage EndSaving.NormalizedEvent.measurable_normalizedField
  have hconst : ∀ (g : DistC) (c : ℝ),
      g ∈ E ↔ LQGMetric.addConst g c ∈ E := by
    intro g c
    exact (EndSaving.NormalizedEvent.normalizedFV2_addConst P h D D' ξ Q cMid cPlus
      par pbar r b q K₁ K₂ obj Z g c).symm
  have hgood : ∀ g ∈ E, ∀ i : ℤ × ℤ, ∀ hi : i ∈ Z,
      g ∈ (obj i).E := by
    intro g hg i hi
    have hlocal : EndSaving.NormalizedEvent.normalizedField g ∈ (obj i).E := by
      rcases hg.1 with ⟨_, _, _, _, _, hloc, _, _, _, _⟩
      exact (hloc i hi).1
    exact ((obj i).E_constant g (-(EndSaving.NormalizedEvent.unitNorm g))).2 hlocal
  have hwindow := EndSaving.RadonNikodym.finiteBump_probability_window_of_objects
    P h hh D D' ξ Q cMid par pbar r Z
    (fun i => LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
    (fun i _ => obj i) hconfig.1 E hE hconst hgood
  have hsum : (∑ i ∈ Z, if hi : i ∈ Z then (obj i).f else 0) =
      (∑ i ∈ Z, (obj i).f) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  simpa only [E, EndSaving.FiniteEvents.bumpSumV2, hsum] using hwindow

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
