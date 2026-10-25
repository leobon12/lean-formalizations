import SupercriticalLQGUniqueness.B2.PfeAxioms.VaryingJointCoordLaw
import SupercriticalLQGUniqueness.B2.PfeAxioms.VaryingContinuousLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology TopologicalSpace
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem joint_lsc_limit_law_of_varying_coupling
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistC) (hN : ℕ → Ω' → DistC) (h' : Ω' → DistC)
    (hh : IsWholePlaneGFF h P) (hh'm : Measurable h')
    (G : ℕ → Ω → C(ℂ × ℂ, EReal))
    (hG : ∀ n, AEMeasurable (G n) P)
    (F : ℕ → Ω' → ℂ × ℂ → EReal)
    (hFc : ∀ n, ∀ᵐ ω ∂P', Continuous (F n ω))
    (D : Ω → LSCMetric)
    (hDm : AEMeasurable (fun ω => (D ω).toLSCFun) P)
    (L : Ω' → LSCMetric) (hLm : Measurable L)
    (hLaw : ∀ n, P'.map (fun ω => (hN n ω, F n ω)) =
      P.map (fun ω => (h ω, (G n ω : ℂ × ℂ → EReal))))
    (hFieldConv : ∀ᵐ ω ∂P',
      Tendsto (fun n => hN n ω) atTop (𝓝 (h' ω)))
    (hConv : ∀ᵐ ω ∂P,
      LSCTendsto (fun n => (G n ω : ℂ × ℂ → EReal))
        (D ω).toLSCFun.1)
    (hConv' : ∀ᵐ ω ∂P',
      LSCTendsto (fun n => F n ω) (L ω).toLSCFun.1) :
    P.map (fun ω => (pairJ (⊤ : Opens ℂ) (h ω), (D ω).toLSCFun)) =
      P'.map (fun ω => (pairJ (⊤ : Opens ℂ) (h' ω), (L ω).toLSCFun)) := by
  classical
  have hLift n := continuous_joint_law_of_varying_point_law
    P P' h (hN n) hh (G n) (hG n) (F n) (hFc n) (hLaw n)
  choose hNm G' hG'm hG'eq hLawC using hLift
  let J : DistC × C(ℂ × ℂ, EReal) → (CoordJ → ℝ) × LSCFun :=
    Prod.map (pairJ (⊤ : Opens ℂ)) B2.LscTop.ofContinuousMap
  have hJm : Measurable J :=
    ((measurable_pairJ _).comp measurable_fst).prodMk
      (B2.LscTop.continuous_ofContinuousMap.measurable.comp measurable_snd)
  have hLawCoord n :
      P.map (fun ω => (pairJ (⊤ : Opens ℂ) (h ω),
          B2.LscTop.ofContinuousMap (G n ω))) =
      P'.map (fun ω => (pairJ (⊤ : Opens ℂ) (hN n ω),
          B2.LscTop.ofContinuousMap (G' n ω))) := by
    have hs : AEMeasurable (fun ω => (h ω, G n ω)) P :=
      hh.measurable.aemeasurable.prodMk (hG n)
    have ht : AEMeasurable (fun ω => (hN n ω, G' n ω)) P' :=
      (hNm n).prodMk (hG'm n).aemeasurable
    have hsrc := AEMeasurable.map_map_of_aemeasurable hJm.aemeasurable hs
    have hdst := AEMeasurable.map_map_of_aemeasurable hJm.aemeasurable ht
    calc
      P.map (fun ω => (pairJ (⊤ : Opens ℂ) (h ω),
          B2.LscTop.ofContinuousMap (G n ω))) =
          (P.map (fun ω => (h ω, G n ω))).map J := by
        simpa only [Function.comp_def, J, Prod.map_apply] using hsrc.symm
      _ = (P'.map (fun ω => (hN n ω, G' n ω))).map J :=
        congrArg (Measure.map J) (hLawC n).symm
      _ = P'.map (fun ω => (pairJ (⊤ : Opens ℂ) (hN n ω),
          B2.LscTop.ofContinuousMap (G' n ω))) := by
        simpa only [Function.comp_def, J, Prod.map_apply] using hdst
  have hConvL : ∀ᵐ ω ∂P,
      Tendsto (fun n => B2.LscTop.ofContinuousMap (G n ω))
        atTop (𝓝 (D ω).toLSCFun) := by
    filter_upwards [hConv] with ω hω
    exact LSCFun.tendsto_of_lscTendsto hω
  have hGeqAll : ∀ᵐ ω ∂P', ∀ n,
      (G' n ω : ℂ × ℂ → EReal) = F n ω :=
    ae_all_iff.mpr hG'eq
  have hConvL' : ∀ᵐ ω ∂P',
      Tendsto (fun n => B2.LscTop.ofContinuousMap (G' n ω))
        atTop (𝓝 (L ω).toLSCFun) := by
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
    exact LSCFun.tendsto_of_lscTendsto hω'
  exact joint_coord_limit_law_of_varying_fields P P' h hh.measurable
    hN hNm h' hh'm
    (fun n ω => B2.LscTop.ofContinuousMap (G n ω))
    (fun n => B2.LscTop.continuous_ofContinuousMap.measurable.comp_aemeasurable (hG n))
    (fun n ω => B2.LscTop.ofContinuousMap (G' n ω))
    (fun n => (B2.LscTop.continuous_ofContinuousMap.measurable.comp (hG'm n)).aemeasurable)
    (fun ω => (D ω).toLSCFun) hDm
    (fun ω => (L ω).toLSCFun)
    (B2.LscTop.measurable_toLSCFun.comp hLm).aemeasurable
    hLawCoord hConvL hFieldConv hConvL'

end SupercriticalLQGUniqueness.B2.PfeAxioms
