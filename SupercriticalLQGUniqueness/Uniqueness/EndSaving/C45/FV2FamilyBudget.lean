import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.RNArithmetic
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.PropCardAE




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem fixed_scale_raw_probability_budget
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
      ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (k Ccard : ℕ)
    (hcard : ∀ᵐ ω ∂P,
      let family : Set (Finset (ℤ × ℤ)) := {Z |
        EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
        EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
          r b q K₁ K₂ obj Z
          (LQGMetric.addFun (h ω) (LQGMetric.testCont
            (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z)))}
      family.Finite ∧ family.ncard ≤ Ccard ^ k) :
    (∑' Z : Finset (ℤ × ℤ),
      P {ω | EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
        EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
          r b q K₁ K₂ obj Z (h ω)}) ≤
      ENNReal.ofReal ((max par.Crn 1) ^ k) * (Ccard ^ k : ℕ) := by
  classical
  let eligible (Z : Finset (ℤ × ℤ)) :=
    EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k
  let proxy (Z : Finset (ℤ × ℤ)) : Set DistC :=
    Classical.choose (raw_fV2_borel_proxy P h hh D D' ξ Q cMid cPlus
      hD hD' par pbar r b q K₁ K₂ hK₁ hK₂ obj Z)
  have hp (Z : Finset (ℤ × ℤ)) :=
    Classical.choose_spec (raw_fV2_borel_proxy P h hh D D' ξ Q cMid cPlus
      hD hD' par pbar r b q K₁ K₂ hK₁ hK₂ obj Z)
  let shift (Z : Finset (ℤ × ℤ)) (ω : Ω) : DistC :=
    LQGMetric.addFun (h ω) (LQGMetric.testCont
      (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z))
  let A (Z : Finset (ℤ × ℤ)) : Set Ω :=
    {ω | eligible Z ∧ h ω ∈ proxy Z}
  let B (Z : Finset (ℤ × ℤ)) : Set Ω :=
    {ω | eligible Z ∧ shift Z ω ∈ proxy Z}
  have hA : ∀ Z, MeasurableSet (A Z) := by
    intro Z
    have he : MeasurableSet {ω : Ω | eligible Z} := by
      by_cases hz : eligible Z <;> simp [hz]
    exact he.inter ((hp Z).1.preimage hh.1.measurable)
  have hB : ∀ Z, MeasurableSet (B Z) := by
    intro Z
    have he : MeasurableSet {ω : Ω | eligible Z} := by
      by_cases hz : eligible Z <;> simp [hz]
    have hm : Measurable (shift Z) :=
      (LQGMetric.measurable_addFun_left _).comp hh.1.measurable
    exact he.inter ((hp Z).1.preimage hm)
  have hEqRaw₀ (Z : Finset (ℤ × ℤ)) :
      P {ω | h ω ∈ proxy Z} =
        P {ω | EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
          r b q K₁ K₂ obj Z (h ω)} := by
    apply measure_congr
    have heq := ae_of_ae_map hh.1.measurable.aemeasurable (hp Z).2.2.2.1
    filter_upwards [heq, EndSaving.NormalizedEvent.normalizedFV2_ae_iff_raw P h hh
      D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z] with ω he hr
    exact propext ((Iff.of_eq he).symm.trans hr)
  have hEqRaw₁ (Z : Finset (ℤ × ℤ)) :
      P {ω | shift Z ω ∈ proxy Z} =
        P (EndSaving.FiniteEvents.ShiftedFV2 P h D D' ξ Q cMid cPlus par pbar
          r b q K₁ K₂ obj Z) := by
    apply measure_congr
    have hm : Measurable (shift Z) :=
      (LQGMetric.measurable_addFun_left _).comp hh.1.measurable
    have heq := ae_of_ae_map hm.aemeasurable (hp Z).2.2.2.2
    filter_upwards [heq, EndSaving.Scaling.normalizedFV2_shifted_ae_iff_raw
      P h hh D D' ξ Q cMid cPlus hD hD' par pbar
      r b q K₁ K₂ obj Z] with ω he hr
    exact propext ((Iff.of_eq he).symm.trans hr)
  have hratio : ∀ Z, P (A Z) ≤
      ENNReal.ofReal ((max par.Crn 1) ^ k) * P (B Z) := by
    intro Z
    by_cases he : eligible Z
    · have hconfig := he.1
      have hzk := he.2
      have hwin := (fV2_probability_window_of_raw_nullMeasurable
        P h hh D D' ξ Q cMid cPlus hD hD' par pbar
        r b q K₁ K₂ hK₁ hK₂ obj Z hconfig).1
      have hbound := probability_le_of_inverse_window par.rn_pos hzk hwin
      have hAeq : P (A Z) =
          P {ω | EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
            r b q K₁ K₂ obj Z (h ω)} := by
        simpa [A, he] using hEqRaw₀ Z
      have hBeq : P (B Z) =
          P (EndSaving.FiniteEvents.ShiftedFV2 P h D D' ξ Q cMid cPlus par pbar
            r b q K₁ K₂ obj Z) := by
        simpa [B, he] using hEqRaw₁ Z
      rw [hAeq, hBeq]
      exact hbound
    · simp [A, B, he]
  have heqAll : ∀ᵐ ω ∂P, ∀ Z : Finset (ℤ × ℤ),
      (ω ∈ B Z) ↔
        (eligible Z ∧ EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
          r b q K₁ K₂ obj Z (shift Z ω)) := by
    apply ae_all_iff.mpr
    intro Z
    by_cases he : eligible Z
    · have hm : Measurable (shift Z) :=
        (LQGMetric.measurable_addFun_left _).comp hh.1.measurable
      have heq := ae_of_ae_map hm.aemeasurable (hp Z).2.2.2.2
      filter_upwards [heq, EndSaving.Scaling.normalizedFV2_shifted_ae_iff_raw
        P h hh D D' ξ Q cMid cPlus hD hD' par pbar
        r b q K₁ K₂ obj Z] with ω hproxy hraw
      simpa only [B, Set.mem_ofPred_eq, he, true_and] using
        ((Iff.of_eq hproxy).symm.trans hraw)
    · exact Filter.Eventually.of_forall (fun ω => by
        simp [B, he])
  have hocc : ∀ᵐ ω ∂P, ∀ s : Finset (Finset (ℤ × ℤ)),
      Set.ncard ((s : Set (Finset (ℤ × ℤ))) ∩ {Z | ω ∈ B Z}) ≤ Ccard ^ k := by
    filter_upwards [heqAll, hcard] with ω he hfin s
    dsimp only at hfin
    have hsub : ((s : Set (Finset (ℤ × ℤ))) ∩ {Z | ω ∈ B Z}) ⊆
        {Z | EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
          EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
            r b q K₁ K₂ obj Z (shift Z ω)} := by
      intro Z hZ
      have hz := (he Z).mp hZ.2
      exact ⟨hz.1.1, hz.1.2, hz.2⟩
    exact (Set.ncard_le_ncard hsub hfin.1).trans hfin.2
  have hsum := tsum_measure_le_of_ratio_and_occupancy P A B hB
    (Ccard ^ k) (ENNReal.ofReal ((max par.Crn 1) ^ k)) hocc hratio
  have hAeq (Z : Finset (ℤ × ℤ)) :
      P (A Z) =
        P {ω | EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
          EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
            r b q K₁ K₂ obj Z (h ω)} := by
    by_cases he : eligible Z
    · simpa [A, eligible, he] using hEqRaw₀ Z
    · have hfalse : ¬(EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k) := he
      have hempty : {ω | EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
          EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
            r b q K₁ K₂ obj Z (h ω)} = (∅ : Set Ω) := by
        ext ω
        constructor
        · intro hω
          exact False.elim (hfalse ⟨hω.1, hω.2.1⟩)
        · intro hω
          simp at hω
      rw [hempty]
      simp [A, he]
  simpa only [hAeq] using hsum

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
