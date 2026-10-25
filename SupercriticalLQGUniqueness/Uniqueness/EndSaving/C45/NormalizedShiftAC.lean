import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.RawRNUniversal
import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.RawFV2Meas




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
open LQGMetric (DistC TestC)

 
theorem normalized_law_map_eq
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    (P.map h).map EndSaving.NormalizedEvent.normalizedField = P.map h := by
  rw [Measure.map_map EndSaving.NormalizedEvent.measurable_normalizedField hh.1.measurable]
  exact Measure.map_congr (by
    filter_upwards [EndSaving.NormalizedEvent.normalizedField_ae_eq_of_normalized P h hh] with ω hω
    exact hω)

 

theorem normalized_shift_law_ac
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (φ : TestC) :
    (P.map (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ))).map
      EndSaving.NormalizedEvent.normalizedField ≪ P.map h := by
  let N := EndSaving.NormalizedEvent.normalizedField
  let sh : Ω → DistC := fun ω =>
    LQGMetric.addFun (h ω) (LQGMetric.testCont φ)
  have hmsh : Measurable sh :=
    (LQGMetric.measurable_addFun_left _).comp hh.1.measurable
  have hmap := normalized_law_map_eq P h hh
  have hAC : (P.map sh).map N ≪ (P.map h).map N := by
    apply Measure.AbsolutelyContinuous.mk
    intro A hA hnull
    obtain ⟨B, hB, hBA⟩ := LQGMetric.GM.exists_pair0_preimage
      (hA.preimage EndSaving.NormalizedEvent.measurable_normalizedField)
      (fun g c => by
        simp only [Set.mem_preimage, EndSaving.NormalizedEvent.normalizedField_addConst])
    have hpre : ∀ f : Ω → DistC, (N ∘ f) ⁻¹' A =
        (fun ω => LQGMetric.pair0 (f ω)) ⁻¹' B := by
      intro f
      ext ω
      exact hBA (f ω)
    have hnullB : LQGMetric.lawPair0 h P B = 0 := by
      rw [LQGMetric.lawPair0, Measure.map_apply
        (show Measurable (fun ω => LQGMetric.pair0 (h ω)) from
          LQGMetric.measurable_pair0.comp hh.1.measurable) hB]
      rw [← hpre h]
      have h0 : (P.map h).map N A = P ((N ∘ h) ⁻¹' A) := by
        rw [Measure.map_map EndSaving.NormalizedEvent.measurable_normalizedField hh.1.measurable,
          Measure.map_apply (EndSaving.NormalizedEvent.measurable_normalizedField.comp hh.1.measurable) hA]
      exact h0 ▸ hnull
    have hshiftB : LQGMetric.lawPair0 sh P B = 0 :=
      (LQGMetric.lawPair0_addFun_ac hh.1 φ) hnullB
    rw [Measure.map_map EndSaving.NormalizedEvent.measurable_normalizedField hmsh,
      Measure.map_apply (EndSaving.NormalizedEvent.measurable_normalizedField.comp hmsh) hA]
    rw [hpre sh]
    rw [LQGMetric.lawPair0, Measure.map_apply
      (show Measurable (fun ω => LQGMetric.pair0 (sh ω)) from
        LQGMetric.measurable_pair0.comp hmsh) hB] at hshiftB
    exact hshiftB
  rw [← hmap]
  exact hAC

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
