import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.ShiftV2




 





set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
open LQGMetric (DistC TestC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem oneBump_probability_window
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (φ : TestC)
    (E : Set DistC) (hE : MeasurableSet E)
    (hconst : ∀ (g : DistC) (c : ℝ),
      g ∈ E ↔ LQGMetric.addConst g c ∈ E)
    (a b : ℝ≥0∞)
    (hwindow : ∀ g ∈ E,
      a ≤ ENNReal.ofReal (LQGMetric.cmDensity φ (LQGMetric.pair0 g)) ∧
      ENNReal.ofReal (LQGMetric.cmDensity φ (LQGMetric.pair0 g)) ≤ b) :
    a * P (sampleEvent h E) ≤
      P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
        (LQGMetric.testCont φ)) E) ∧
    P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
        (LQGMetric.testCont φ)) E) ≤ b * P (sampleEvent h E) := by
  obtain ⟨A, hA, hEq⟩ := LQGMetric.GM.exists_pair0_preimage hE
    (fun g c => (hconst g c).symm)
  let density : (LQGMetric.TestC0 → ℝ) → ℝ≥0∞ :=
    fun ξ => ENNReal.ofReal (LQGMetric.cmDensity φ ξ)
  have hdens : Measurable density :=
    ENNReal.measurable_ofReal.comp (LQGMetric.measurable_cmDensity φ)
  have hp : Measurable (fun ω => LQGMetric.pair0 (h ω)) :=
    LQGMetric.measurable_pair0_comp hh.1
  have hs : (fun ω => LQGMetric.pair0 (h ω)) ⁻¹' A = sampleEvent h E := by
    ext ω
    exact (hEq (h ω)).symm
  have hshift : (fun ω => LQGMetric.pair0
      (LQGMetric.addFun (h ω) (LQGMetric.testCont φ))) ⁻¹' A =
      sampleEvent (fun ω => LQGMetric.addFun (h ω)
        (LQGMetric.testCont φ)) E := by
    ext ω
    exact (hEq _).symm
  have hmeasure : P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
      (LQGMetric.testCont φ)) E) =
      ∫⁻ ω in sampleEvent h E, density (LQGMetric.pair0 (h ω)) ∂P := by
    rw [← hshift, ← hs, ← Measure.map_apply
      (LQGMetric.measurable_pair0_addFun hh.1 φ) hA]
    change LQGMetric.lawPair0
      (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) P A = _
    rw [LQGMetric.lawPair0_addFun_eq_withDensity hh.1 φ]
    rw [withDensity_apply _ hA, LQGMetric.lawPair0]
    exact setLIntegral_map hA hdens hp
  rw [hmeasure]
  constructor
  · calc
      a * P (sampleEvent h E) = ∫⁻ _ω in sampleEvent h E, a ∂P :=
        (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ ω in sampleEvent h E,
          density (LQGMetric.pair0 (h ω)) ∂P := by
        apply setLIntegral_mono' (hE.preimage hh.1.measurable)
        intro ω hω
        exact (hwindow (h ω) hω).1
  · calc
      (∫⁻ ω in sampleEvent h E,
          density (LQGMetric.pair0 (h ω)) ∂P) ≤
          ∫⁻ _ω in sampleEvent h E, b ∂P := by
        apply setLIntegral_mono' (hE.preimage hh.1.measurable)
        intro ω hω
        exact (hwindow (h ω) hω).2
      _ = b * P (sampleEvent h E) := setLIntegral_const _ _

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
