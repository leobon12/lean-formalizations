import SupercriticalLQGUniqueness.B2.PfeAxioms.CouplingMeasurable
import SupercriticalLQGUniqueness.B2.PfeAxioms.ContinuousCouplingLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem measurable_continuousMap_coe :
    Measurable (fun g : C(ℂ × ℂ, EReal) => (g : ℂ × ℂ → EReal)) := by
  rw [measurable_iff_comap_le]
  exact continuousMap_comap_eq.le

 


theorem continuous_joint_law_of_point_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistC) (h' : Ω' → DistC)
    (hh : IsWholePlaneGFF h P) (hh'm : Measurable h')
    (G : Ω → C(ℂ × ℂ, EReal)) (hG : AEMeasurable G P)
    (F : Ω' → ℂ × ℂ → EReal)
    (hFc : ∀ᵐ ω ∂P', Continuous (F ω))
    (hLaw : P'.map (fun ω => (h' ω, F ω)) =
      P.map (fun ω => (h ω, (G ω : ℂ × ℂ → EReal)))) :
    ∃ G' : Ω' → C(ℂ × ℂ, EReal),
      Measurable G' ∧
      (∀ᵐ ω ∂P', (G' ω : ℂ × ℂ → EReal) = F ω) ∧
      P'.map (fun ω => (h' ω, G' ω)) =
        P.map (fun ω => (h ω, G ω)) := by
  let e := Prod.map (id : DistC → DistC)
    (fun g : C(ℂ × ℂ, EReal) => (g : ℂ × ℂ → EReal))
  have hem : Measurable e :=
    measurable_fst.prodMk (measurable_continuousMap_coe.comp measurable_snd)
  have hGraw : AEMeasurable
      (fun ω => (G ω : ℂ × ℂ → EReal)) P :=
    measurable_continuousMap_coe.comp_aemeasurable hG
  have hsrc : AEMeasurable
      (fun ω => (h ω, (G ω : ℂ × ℂ → EReal))) P :=
    hh.measurable.aemeasurable.prodMk hGraw
  have hnon : ∀ a : DistC × (ℂ × ℂ → EReal),
      P.map (fun ω => (h ω, (G ω : ℂ × ℂ → EReal))) ≠ Measure.dirac a :=
    fun a => gff_joint_law_ne_dirac P h hh _ hGraw a
  have hdst : AEMeasurable (fun ω => (h' ω, F ω)) P' :=
    aemeasurable_of_map_eq_nondirac P P' _ _ hsrc hnon hLaw
  have hFm : AEMeasurable F P' := measurable_snd.comp_aemeasurable hdst
  obtain ⟨G', hG'm, hG'eq⟩ :=
    exists_measurable_continuous_version P' F hFm hFc
  refine ⟨G', hG'm, hG'eq, ?_⟩
  apply continuous_joint_law_map_injective
  have hdstMap : (P'.map (fun ω => (h' ω, G' ω))).map e =
      P'.map (fun ω => (h' ω, (G' ω : ℂ × ℂ → EReal))) := by
    rw [AEMeasurable.map_map_of_aemeasurable hem.aemeasurable
      (hh'm.prodMk hG'm).aemeasurable]
    rfl
  have hsrcMap : (P.map (fun ω => (h ω, G ω))).map e =
      P.map (fun ω => (h ω, (G ω : ℂ × ℂ → EReal))) := by
    rw [AEMeasurable.map_map_of_aemeasurable hem.aemeasurable
      (hh.measurable.aemeasurable.prodMk hG)]
    rfl
  rw [hdstMap, hsrcMap]
  exact (Measure.map_congr (hG'eq.mono fun ω hω => by simp [hω])).trans hLaw

end SupercriticalLQGUniqueness.B2.PfeAxioms
