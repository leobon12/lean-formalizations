import SupercriticalLQGUniqueness.B2.PfeAxioms.ContinuousCouplingVersion
import Mathlib.MeasureTheory.MeasurableSpace.Prod

 

set_option autoImplicit false
noncomputable section

open MeasureTheory MeasurableSpace

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem continuousMap_comap_eq :
    MeasurableSpace.comap
      (fun g : C(ℂ × ℂ, EReal) => (g : ℂ × ℂ → EReal))
      (inferInstance : MeasurableSpace (ℂ × ℂ → EReal)) =
    (inferInstance : MeasurableSpace C(ℂ × ℂ, EReal)) := by
  rw [MeasurableSpace.pi, ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp_rw [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

 


theorem continuous_joint_law_map_injective
    {A : Type*} [MeasurableSpace A] :
    Function.Injective (Measure.map
      (Prod.map (id : A → A)
        (fun g : C(ℂ × ℂ, EReal) => (g : ℂ × ℂ → EReal)))) := by
  let e := Prod.map (id : A → A)
    (fun g : C(ℂ × ℂ, EReal) => (g : ℂ × ℂ → EReal))
  have hc : MeasurableSpace.comap e
      (inferInstance : MeasurableSpace (A × (ℂ × ℂ → EReal))) =
      (inferInstance : MeasurableSpace (A × C(ℂ × ℂ, EReal))) := by
    simpa only [e, Prod.instMeasurableSpace, MeasurableSpace.comap_prodMap,
      MeasurableSpace.comap_id, continuousMap_comap_eq]
  intro μ ν h
  apply Measure.ext
  intro s hs
  have hs' : (MeasurableSpace.comap e
      (inferInstance : MeasurableSpace (A × (ℂ × ℂ → EReal)))).MeasurableSet' s := by
    rw [hc]
    exact hs
  obtain ⟨t, ht, rfl⟩ := hs'
  have hem : Measurable e := by
    rw [measurable_iff_comap_le]
    exact hc.le
  calc
    μ (e ⁻¹' t) = (Measure.map e μ) t := (Measure.map_apply hem ht).symm
    _ = (Measure.map e ν) t := congrArg (fun ρ : Measure (A × (ℂ × ℂ → EReal)) => ρ t) h
    _ = ν (e ⁻¹' t) := Measure.map_apply hem ht

end SupercriticalLQGUniqueness.B2.PfeAxioms
