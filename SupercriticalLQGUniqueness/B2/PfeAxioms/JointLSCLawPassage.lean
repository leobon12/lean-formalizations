import SupercriticalLQGUniqueness.B2.PfeAxioms.CouplingContinuousLaw
import SupercriticalLQGUniqueness.B2.PfeAxioms.StaticJointLawLimit
import SupercriticalLQGUniqueness.B2.LscTop.Limits

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem joint_lsc_limit_law_of_continuous_coupling
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistC) (h' : Ω' → DistC)
    (hh : IsWholePlaneGFF h P) (hh'm : Measurable h')
    (G : ℕ → Ω → C(ℂ × ℂ, EReal))
    (hG : ∀ n, AEMeasurable (G n) P)
    (F : ℕ → Ω' → ℂ × ℂ → EReal)
    (hFc : ∀ n, ∀ᵐ ω ∂P', Continuous (F n ω))
    (D : Ω → LSCMetric)
    (hDm : AEMeasurable (fun ω => (D ω).toLSCFun) P)
    (L : Ω' → LSCMetric) (hLm : Measurable L)
    (hLaw : ∀ n, P'.map (fun ω => (h' ω, F n ω)) =
      P.map (fun ω => (h ω, (G n ω : ℂ × ℂ → EReal))))
    (hConv : ∀ᵐ ω ∂P,
      LSCTendsto (fun n => (G n ω : ℂ × ℂ → EReal)) (D ω).toLSCFun.1)
    (hConv' : ∀ᵐ ω ∂P',
      LSCTendsto (fun n => F n ω) (L ω).toLSCFun.1) :
    P.map (fun ω => (h ω, (D ω).toLSCFun)) =
      P'.map (fun ω => (h' ω, (L ω).toLSCFun)) := by
  classical
  have hLift n := continuous_joint_law_of_point_law P P' h h' hh hh'm
    (G n) (hG n) (F n) (hFc n) (hLaw n)
  choose G' hG'm hG'eq hLawC using hLift
  let T : DistC × C(ℂ × ℂ, EReal) → DistC × LSCFun :=
    Prod.map id B2.LscTop.ofContinuousMap
  have hTm : Measurable T :=
    measurable_fst.prodMk
      (B2.LscTop.continuous_ofContinuousMap.measurable.comp measurable_snd)
  have hLawL n :
      P.map (fun ω => (h ω, B2.LscTop.ofContinuousMap (G n ω))) =
      P'.map (fun ω => (h' ω, B2.LscTop.ofContinuousMap (G' n ω))) := by
    have hs : AEMeasurable (fun ω => (h ω, G n ω)) P :=
      hh.measurable.aemeasurable.prodMk (hG n)
    have ht : AEMeasurable (fun ω => (h' ω, G' n ω)) P' :=
      (hh'm.prodMk (hG'm n)).aemeasurable
    have hsrc := AEMeasurable.map_map_of_aemeasurable hTm.aemeasurable hs
    have hdst := AEMeasurable.map_map_of_aemeasurable hTm.aemeasurable ht
    calc
      P.map (fun ω => (h ω, B2.LscTop.ofContinuousMap (G n ω))) =
          (P.map (fun ω => (h ω, G n ω))).map T := by
        simpa only [Function.comp_def, T, Prod.map_apply, id_eq] using hsrc.symm
      _ = (P'.map (fun ω => (h' ω, G' n ω))).map T :=
        congrArg (Measure.map T) (hLawC n).symm
      _ = P'.map (fun ω => (h' ω, B2.LscTop.ofContinuousMap (G' n ω))) := by
        simpa only [Function.comp_def, T, Prod.map_apply, id_eq] using hdst
  have hConvL : ∀ᵐ ω ∂P,
      Tendsto (fun n => (h ω, B2.LscTop.ofContinuousMap (G n ω)))
        atTop (𝓝 (h ω, (D ω).toLSCFun)) := by
    filter_upwards [hConv] with ω hω
    have hω' : LSCTendsto
        (fun n => (B2.LscTop.ofContinuousMap (G n ω)).1)
        (D ω).toLSCFun.1 := hω
    exact tendsto_const_nhds.prodMk_nhds
      (LSCFun.tendsto_of_lscTendsto hω')
  have hGeqAll : ∀ᵐ ω ∂P', ∀ n,
      (G' n ω : ℂ × ℂ → EReal) = F n ω :=
    ae_all_iff.mpr hG'eq
  have hConvL' : ∀ᵐ ω ∂P',
      Tendsto (fun n => (h' ω, B2.LscTop.ofContinuousMap (G' n ω)))
        atTop (𝓝 (h' ω, (L ω).toLSCFun)) := by
    filter_upwards [hConv', hGeqAll] with ω hω hEq
    have hω' : LSCTendsto
        (fun n => (B2.LscTop.ofContinuousMap (G' n ω)).1)
        (L ω).toLSCFun.1 := by
      have hfEq : (fun n => (B2.LscTop.ofContinuousMap (G' n ω)).1) =
          (fun n => F n ω) := by
        funext n
        exact hEq n
      rw [hfEq]
      exact hω
    exact tendsto_const_nhds.prodMk_nhds
      (LSCFun.tendsto_of_lscTendsto hω')
  letI : OpensMeasurableSpace LSCFun :=
    ⟨by
      change borel LSCFun ≤ (inferInstance : MeasurableSpace LSCFun)
      rw [BorelSpace.measurable_eq (α := LSCFun)]⟩
  have hmG : ∀ n, AEMeasurable
      (fun ω => B2.LscTop.ofContinuousMap (G n ω)) P := fun n =>
    B2.LscTop.continuous_ofContinuousMap.measurable.comp_aemeasurable (hG n)
  have hmG' : ∀ n, AEMeasurable
      (fun ω => B2.LscTop.ofContinuousMap (G' n ω)) P' := fun n =>
    (B2.LscTop.continuous_ofContinuousMap.measurable.comp (hG'm n)).aemeasurable
  exact static_joint_limit_law_eq P P' h h' hh.measurable hh'm
    (fun n ω => B2.LscTop.ofContinuousMap (G n ω))
    (fun n ω => B2.LscTop.ofContinuousMap (G' n ω))
    (fun ω => (D ω).toLSCFun) (fun ω => (L ω).toLSCFun)
    hmG hmG'
    hDm
    (B2.LscTop.measurable_toLSCFun.comp hLm).aemeasurable
    hLawL
    (hConvL.mono fun ω hω =>
      (continuous_snd.tendsto (h ω, (D ω).toLSCFun)).comp hω)
    (hConvL'.mono fun ω hω =>
      (continuous_snd.tendsto (h' ω, (L ω).toLSCFun)).comp hω)

 

theorem aemeasurable_lsc_limit_of_continuous_approximants
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G : ℕ → Ω → C(ℂ × ℂ, EReal))
    (hG : ∀ n, AEMeasurable (G n) P)
    (D : Ω → LSCMetric)
    (hConv : ∀ᵐ ω ∂P,
      LSCTendsto (fun n => (G n ω : ℂ × ℂ → EReal)) (D ω).toLSCFun.1) :
    AEMeasurable (fun ω => (D ω).toLSCFun) P := by
  have hApprox : ∀ n, AEMeasurable
      (fun ω => B2.LscTop.ofContinuousMap (G n ω)) P := fun n =>
    B2.LscTop.continuous_ofContinuousMap.measurable.comp_aemeasurable (hG n)
  have hTend : ∀ᵐ ω ∂P,
      Tendsto (fun n => B2.LscTop.ofContinuousMap (G n ω))
        atTop (𝓝 (D ω).toLSCFun) := by
    filter_upwards [hConv] with ω hω
    have hω' : LSCTendsto
        (fun n => (B2.LscTop.ofContinuousMap (G n ω)).1)
        (D ω).toLSCFun.1 := hω
    exact LSCFun.tendsto_of_lscTendsto hω'
  exact aemeasurable_of_tendsto_metrizable_ae atTop hApprox hTend

end SupercriticalLQGUniqueness.B2.PfeAxioms
