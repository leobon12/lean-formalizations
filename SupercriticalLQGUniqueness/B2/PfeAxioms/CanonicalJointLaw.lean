import SupercriticalLQGUniqueness.B2.PfeAxioms.CanonicalLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.JointLawDG20Strong

set_option autoImplicit false
noncomputable section

open MeasureTheory LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem ae_target_eq_canonical_of_joint_law
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (h : Ω → DistC) (h' : Ω' → DistC)
    (hh : Measurable h) (hh' : Measurable h')
    (D : Ω → LSCMetric) (L : Ω' → LSCMetric)
    (hL : Measurable L)
    (C : DistC → LSCFun) (hC : Measurable C)
    (hDC : ∀ᵐ ω ∂P, C (h ω) = (D ω).toLSCFun)
    (hLaw : P.map (fun ω => (h ω, (D ω).toLSCFun)) =
      P'.map (fun ω => (h' ω, (L ω).toLSCFun))) :
    ∀ᵐ ω ∂P', C (h' ω) = (L ω).toLSCFun := by
  have hDm : AEMeasurable (fun ω => (D ω).toLSCFun) P :=
    (hC.comp hh).aemeasurable.congr hDC
  have hPm : AEMeasurable (fun ω => (h ω, (D ω).toLSCFun)) P :=
    hh.aemeasurable.prodMk hDm
  have hP'm : AEMeasurable (fun ω => (h' ω, (L ω).toLSCFun)) P' :=
    (hh'.prodMk (B2.LscTop.measurable_toLSCFun.comp hL)).aemeasurable
  have hEvent : MeasurableSet {p : DistC × LSCFun | C p.1 = p.2} :=
    measurableSet_eq_fun (hC.comp measurable_fst) measurable_snd
  have hSource : ∀ᵐ ω ∂P, (h ω, (D ω).toLSCFun) ∈
      {p : DistC × LSCFun | C p.1 = p.2} := hDC
  have hMap : ∀ᵐ p ∂P.map (fun ω => (h ω, (D ω).toLSCFun)),
      p ∈ {p : DistC × LSCFun | C p.1 = p.2} :=
    (ae_map_iff hPm hEvent).2 hSource
  rw [hLaw] at hMap
  exact (ae_map_iff hP'm hEvent).1 hMap

end SupercriticalLQGUniqueness.B2.PfeAxioms
