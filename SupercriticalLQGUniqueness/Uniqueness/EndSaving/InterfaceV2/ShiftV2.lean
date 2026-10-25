import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.InterfaceV2
import LQGMetric.Papers.GM.S5.Prop43bInv




 




set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
open LQGMetric (DistC TestC)

 


theorem oneBump_event_ac {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (φ : TestC)
    (E : Set DistC) (hE : MeasurableSet E)
    (hconst : ∀ (g : DistC) (c : ℝ), g ∈ E ↔ LQGMetric.addConst g c ∈ E)
    (hzero : P (sampleEvent h E) = 0) :
    P (sampleEvent (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) E) = 0 := by
  obtain ⟨A, hA, hEq⟩ := LQGMetric.GM.exists_pair0_preimage hE
    (fun g c => (hconst g c).symm)
  have hzeroA : LQGMetric.lawPair0 h P A = 0 := by
    rw [LQGMetric.lawPair0,
      Measure.map_apply (LQGMetric.measurable_pair0_comp hh.1) hA]
    have hs : (fun ω => LQGMetric.pair0 (h ω)) ⁻¹' A = sampleEvent h E := by
      ext ω
      exact (hEq (h ω)).symm
    rw [hs]
    exact hzero
  have hshiftA : LQGMetric.lawPair0
      (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) P A = 0 :=
    (LQGMetric.lawPair0_addFun_ac hh.1 φ) hzeroA
  rw [LQGMetric.lawPair0,
    Measure.map_apply (LQGMetric.measurable_pair0_addFun hh.1 φ) hA] at hshiftA
  have hs : (fun ω => LQGMetric.pair0
      (LQGMetric.addFun (h ω) (LQGMetric.testCont φ))) ⁻¹' A =
      sampleEvent (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) E := by
    ext ω
    exact (hEq _).symm
  rw [← hs]
  exact hshiftA

 

theorem oneBump_event_ac_reverse {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (φ : TestC)
    (E : Set DistC) (hE : MeasurableSet E)
    (hconst : ∀ (g : DistC) (c : ℝ), g ∈ E ↔ LQGMetric.addConst g c ∈ E)
    (hzero : P (sampleEvent
      (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) E) = 0) :
    P (sampleEvent h E) = 0 := by
  obtain ⟨A, hA, hEq⟩ := LQGMetric.GM.exists_pair0_preimage hE
    (fun g c => (hconst g c).symm)
  have hshiftA : LQGMetric.lawPair0
      (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) P A = 0 := by
    rw [LQGMetric.lawPair0,
      Measure.map_apply (LQGMetric.measurable_pair0_addFun hh.1 φ) hA]
    have hs : (fun ω => LQGMetric.pair0
        (LQGMetric.addFun (h ω) (LQGMetric.testCont φ))) ⁻¹' A =
        sampleEvent (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) E := by
      ext ω
      exact (hEq _).symm
    rw [hs]
    exact hzero
  have hzeroA : LQGMetric.lawPair0 h P A = 0 :=
    (LQGMetric.lawPair0_ac_addFun hh.1 φ) hshiftA
  rw [LQGMetric.lawPair0,
    Measure.map_apply (LQGMetric.measurable_pair0_comp hh.1) hA] at hzeroA
  have hs : (fun ω => LQGMetric.pair0 (h ω)) ⁻¹' A = sampleEvent h E := by
    ext ω
    exact (hEq (h ω)).symm
  rw [← hs]
  exact hzeroA

 

theorem finiteBump_event_ac {Ω ι : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (Z : Finset ι) (f : ι → TestC)
    (E : Set DistC) (hE : MeasurableSet E)
    (hconst : ∀ (g : DistC) (c : ℝ), g ∈ E ↔ LQGMetric.addConst g c ∈ E)
    (hzero : P (sampleEvent h E) = 0) :
    P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
      (LQGMetric.testCont (∑ i ∈ Z, f i))) E) = 0 :=
  oneBump_event_ac P h hh (∑ i ∈ Z, f i) E hE hconst hzero

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
