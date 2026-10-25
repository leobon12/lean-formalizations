import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.RawRNWindow
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.LocalShiftV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.SampleV2




set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC TestC)

 

theorem ae_predicate_after_test_shift
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (φ : TestC)
    (E : Set DistC) (hE : MeasurableSet E)
    (hconst : ∀ g : DistC, ∀ c : ℝ,
      g ∈ E ↔ LQGMetric.addConst g c ∈ E)
    (hae : ∀ᵐ ω ∂P, h ω ∈ E) :
    ∀ᵐ ω ∂P,
      LQGMetric.addFun (h ω) (LQGMetric.testCont φ) ∈ E := by
  have hzero : P (EndSaving.InterfaceV2.sampleEvent h Eᶜ) = 0 := by
    apply (measure_eq_zero_iff_ae_notMem).2
    filter_upwards [hae] with ω hω
    simpa [EndSaving.InterfaceV2.sampleEvent] using hω
  have hconst' : ∀ g : DistC, ∀ c : ℝ,
      g ∈ Eᶜ ↔ LQGMetric.addConst g c ∈ Eᶜ := by
    intro g c
    simpa using not_congr (hconst g c)
  have hs := EndSaving.InterfaceV2.oneBump_event_ac P h hh φ Eᶜ hE.compl hconst' hzero
  have hs' := (measure_eq_zero_iff_ae_notMem).1 hs
  filter_upwards [hs'] with ω hω
  simpa [EndSaving.InterfaceV2.sampleEvent] using hω

 

theorem local_event_subTest_shifted_ae
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (K : Set ℂ) (φ ψ : TestC)
    (hφ : ∃ ε > 0,
      Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K))
    (E : Set DistC) (hE : MeasurableSet E)
    (hconst : ∀ g : DistC, ∀ c : ℝ,
      g ∈ E ↔ LQGMetric.addConst g c ∈ E)
    (hlocal : ∃ E₀ : Set DistC,
      @MeasurableSet DistC
        (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K) E₀ ∧
      E =ᵐ[P.map h] E₀) :
    ∀ᵐ ω ∂P,
      LQGMetric.GM.subTest
        (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ)) φ ∈ E ↔
      LQGMetric.addFun (h ω) (LQGMetric.testCont ψ) ∈ E := by
  let A : Set DistC := {g | LQGMetric.GM.subTest g φ ∈ E ↔ g ∈ E}
  have hA : MeasurableSet A := by
    have hm : Measurable (fun g : DistC => LQGMetric.GM.subTest g φ) := by
      simpa [EndSaving.Choices.subTest_eq_addFun] using
        LQGMetric.measurable_addFun_left (LQGMetric.testCont (-φ))
    exact (hm hE).iff hE
  have hAconst : ∀ g : DistC, ∀ c : ℝ,
      g ∈ A ↔ LQGMetric.addConst g c ∈ A := by
    intro g c
    have hcomm : LQGMetric.GM.subTest (LQGMetric.addConst g c) φ =
        LQGMetric.addConst (LQGMetric.GM.subTest g φ) c := by
      simp only [LQGMetric.GM.subTest, LQGMetric.addConst,
        LQGMetric.addFun, add_assoc]
      rw [add_comm (LQGMetric.ofCont (ContinuousMap.const ℂ c))
        (LQGMetric.ofCont (-LQGMetric.testCont φ))]
    change (LQGMetric.GM.subTest g φ ∈ E ↔ g ∈ E) ↔
      (LQGMetric.GM.subTest (LQGMetric.addConst g c) φ ∈ E ↔
        LQGMetric.addConst g c ∈ E)
    rw [hcomm, ← hconst, ← hconst]
  have hbase : ∀ᵐ ω ∂P, h ω ∈ A :=
    EndSaving.InterfaceV2.local_event_subTest_ae P h hh K φ hφ E hE hconst hlocal
  exact ae_predicate_after_test_shift P h hh ψ A hA hAconst hbase

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
