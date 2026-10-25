import SupercriticalLQGUniqueness.B2.PfeAxioms.JointLawLimit
import SupercriticalLQGUniqueness.B2.LscTop.Limits
import LQGMetric.Field.StandardBorelRange
import LQGMetric.Field.RandomDistVersion

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology TopologicalSpace
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem continuous_pairJ_top :
    Continuous (pairJ (⊤ : Opens ℂ) : DistC → CoordJ → ℝ) := by
  change Continuous (fun h : DistC => fun c : CoordJ => h (comb (⊤ : Opens ℂ) c))
  refine continuous_pi fun c => ?_
  exact continuous_eval_const _

 

theorem joint_coord_limit_law_of_varying_fields
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (hN : ℕ → Ω' → DistC)
    (hhN : ∀ n, AEMeasurable (hN n) P')
    (h' : Ω' → DistC) (hh' : Measurable h')
    (G : ℕ → Ω → LSCFun) (hGm : ∀ n, AEMeasurable (G n) P)
    (F : ℕ → Ω' → LSCFun) (hFm : ∀ n, AEMeasurable (F n) P')
    (D : Ω → LSCFun) (hDm : AEMeasurable D P)
    (L : Ω' → LSCFun) (hLm : AEMeasurable L P')
    (hLaw : ∀ n,
      P.map (fun ω => (pairJ (⊤ : Opens ℂ) (h ω), G n ω)) =
      P'.map (fun ω => (pairJ (⊤ : Opens ℂ) (hN n ω), F n ω)))
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (𝓝 (D ω)))
    (hConvField : ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω) atTop (𝓝 (h' ω)))
    (hConv' : ∀ᵐ ω ∂P', Tendsto (fun n => F n ω) atTop (𝓝 (L ω))) :
    P.map (fun ω => (pairJ (⊤ : Opens ℂ) (h ω), D ω)) =
      P'.map (fun ω => (pairJ (⊤ : Opens ℂ) (h' ω), L ω)) := by
  let j : DistC → CoordJ → ℝ := pairJ (⊤ : Opens ℂ)
  have hjm : Measurable j := measurable_pairJ _
  apply joint_limit_law_eq_of_finite_laws P P'
    (fun n ω => (j (h ω), G n ω))
    (fun n ω => (j (hN n ω), F n ω))
    (fun ω => (j (h ω), D ω))
    (fun ω => (j (h' ω), L ω))
  · intro n
    exact (hjm.comp hh).aemeasurable.prodMk (hGm n)
  · intro n
    exact (hjm.comp_aemeasurable (hhN n)).prodMk (hFm n)
  · exact (hjm.comp hh).aemeasurable.prodMk hDm
  · exact (hjm.comp hh').aemeasurable.prodMk hLm
  · exact hLaw
  · filter_upwards [hConv] with ω hω
    exact tendsto_const_nhds.prodMk_nhds hω
  · filter_upwards [hConvField, hConv'] with ω hω hω'
    exact ((continuous_pairJ_top.tendsto _).comp hω).prodMk_nhds hω'

 


theorem joint_lsc_law_of_pairJ_law
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (h : Ω → DistC) (h' : Ω' → DistC)
    (hh : Measurable h) (hh' : Measurable h')
    (D : Ω → LSCFun) (L : Ω' → LSCFun)
    (hDm : AEMeasurable D P) (hLm : AEMeasurable L P')
    (hLaw : P.map (fun ω => (pairJ (⊤ : Opens ℂ) (h ω), D ω)) =
      P'.map (fun ω => (pairJ (⊤ : Opens ℂ) (h' ω), L ω))) :
    P.map (fun ω => (h ω, D ω)) =
      P'.map (fun ω => (h' ω, L ω)) := by
  let I : (CoordJ → ℝ) × LSCFun → DistC × LSCFun :=
    Prod.map (pairJInv (⊤ : Opens ℂ)) id
  have hIm : Measurable I :=
    ((measurable_pairJInv _).comp measurable_fst).prodMk measurable_snd
  have hm : AEMeasurable
      (fun ω => (pairJ (⊤ : Opens ℂ) (h ω), D ω)) P :=
    ((measurable_pairJ _).comp hh).aemeasurable.prodMk hDm
  have hm' : AEMeasurable
      (fun ω => (pairJ (⊤ : Opens ℂ) (h' ω), L ω)) P' :=
    ((measurable_pairJ _).comp hh').aemeasurable.prodMk hLm
  have hMap := congrArg (Measure.map I) hLaw
  rw [AEMeasurable.map_map_of_aemeasurable hIm.aemeasurable hm,
    AEMeasurable.map_map_of_aemeasurable hIm.aemeasurable hm'] at hMap
  simpa only [Function.comp_def, I, Prod.map_apply, id_eq, pairJInv_pairJ] using hMap

end SupercriticalLQGUniqueness.B2.PfeAxioms
