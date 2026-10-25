import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.AEMeasurable
import SupercriticalLQGUniqueness.Frozen.LSCTendsto

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem exists_measurable_continuous_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ℂ × ℂ → EReal)
    (hFm : AEMeasurable F P)
    (hFc : ∀ᵐ ω ∂P, Continuous (F ω)) :
    ∃ G : Ω → C(ℂ × ℂ, EReal),
      Measurable G ∧ ∀ᵐ ω ∂P, (G ω : ℂ × ℂ → EReal) = F ω := by
  classical
  obtain ⟨B, hBae, hBm, hBsub⟩ :=
    IsMeasurablyGenerated.exists_measurable_subset
      (hFc.and hFm.ae_eq_mk)
  let G : Ω → C(ℂ × ℂ, EReal) := fun ω =>
    if hω : ω ∈ B then ⟨F ω, (hBsub hω).1⟩
    else ⟨fun _ => 0, continuous_const⟩
  refine ⟨G, ?_, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro q
    have heq : (fun ω => G ω q) =
        (fun ω => if ω ∈ B then (hFm.mk F ω) q else (0 : EReal)) := by
      funext ω
      by_cases hω : ω ∈ B
      · simp [G, hω, (hBsub hω).2]
      · simp [G, hω]
    rw [heq]
    have hm : Measurable (fun ω => (hFm.mk F ω) q) := hFm.measurable_mk.eval
    exact hm.ite hBm measurable_const
  · have hBae' : ∀ᵐ ω ∂P, ω ∈ B := hBae
    filter_upwards [hBae'] with ω hω
    simp [G, hω]

end SupercriticalLQGUniqueness.B2.PfeAxioms
