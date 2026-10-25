import SupercriticalLQGUniqueness.B2.PfeAxioms.CouplingContinuousLaw

 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem continuous_joint_law_of_varying_point_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistC) (hN : Ω' → DistC)
    (hh : IsWholePlaneGFF h P)
    (G : Ω → C(ℂ × ℂ, EReal)) (hG : AEMeasurable G P)
    (F : Ω' → ℂ × ℂ → EReal)
    (hFc : ∀ᵐ ω ∂P', Continuous (F ω))
    (hLaw : P'.map (fun ω => (hN ω, F ω)) =
      P.map (fun ω => (h ω, (G ω : ℂ × ℂ → EReal)))) :
    AEMeasurable hN P' ∧
    ∃ G' : Ω' → C(ℂ × ℂ, EReal),
      Measurable G' ∧
      (∀ᵐ ω ∂P', (G' ω : ℂ × ℂ → EReal) = F ω) ∧
      P'.map (fun ω => (hN ω, G' ω)) =
        P.map (fun ω => (h ω, G ω)) := by
  have hGraw : AEMeasurable (fun ω => (G ω : ℂ × ℂ → EReal)) P :=
    measurable_continuousMap_coe.comp_aemeasurable hG
  have hsrc : AEMeasurable
      (fun ω => (h ω, (G ω : ℂ × ℂ → EReal))) P :=
    hh.measurable.aemeasurable.prodMk hGraw
  have hnon : ∀ a : DistC × (ℂ × ℂ → EReal),
      P.map (fun ω => (h ω, (G ω : ℂ × ℂ → EReal))) ≠ Measure.dirac a :=
    fun a => gff_joint_law_ne_dirac P h hh _ hGraw a
  have hdst : AEMeasurable (fun ω => (hN ω, F ω)) P' :=
    aemeasurable_of_map_eq_nondirac P P' _ _ hsrc hnon hLaw
  have hNm : AEMeasurable hN P' :=
    measurable_fst.comp_aemeasurable hdst
  let hNv : Ω' → DistC := hNm.mk hN
  have hNvm : Measurable hNv := hNm.measurable_mk
  have hNveq : hN =ᵐ[P'] hNv := hNm.ae_eq_mk
  have hLawV : P'.map (fun ω => (hNv ω, F ω)) =
      P.map (fun ω => (h ω, (G ω : ℂ × ℂ → EReal))) := by
    calc
      P'.map (fun ω => (hNv ω, F ω)) =
          P'.map (fun ω => (hN ω, F ω)) :=
        Measure.map_congr (hNveq.mono fun _ he => by simp [he]) |>.symm
      _ = _ := hLaw
  obtain ⟨G', hG'm, hG'eq, hLift⟩ :=
    continuous_joint_law_of_point_law P P' h hNv hh hNvm G hG F hFc hLawV
  refine ⟨hNm, G', hG'm, hG'eq, ?_⟩
  calc
    P'.map (fun ω => (hN ω, G' ω)) =
        P'.map (fun ω => (hNv ω, G' ω)) :=
      Measure.map_congr (hNveq.mono fun _ he => by simp [he])
    _ = _ := hLift

end SupercriticalLQGUniqueness.B2.PfeAxioms
