import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPPCoupling
import SupercriticalLQGUniqueness.B2.LscTop.LFPP
import SupercriticalLQGUniqueness.Frozen.LSCMetricToLSCFun

 


set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology MeasureTheory LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def finiteLSCMetric (D : ContMetric) : LSCMetric :=
  ⟨fun p => edist (D.pt p.1) (D.pt p.2),
    ⟨fun x => edist_self _,
      fun _ _ h => by
        have hh := edist_eq_zero.mp h
        exact congrArg D.unpt hh,
      fun x y => edist_comm _ _,
      fun x y z => edist_triangle _ _ _⟩,
    (continuous_edist.comp
      ((D.continuous_pt.comp continuous_fst).prodMk
        (D.continuous_pt.comp continuous_snd))).lowerSemicontinuous⟩

@[simp] theorem finiteLSCMetric_apply (D : ContMetric) (p : ℂ × ℂ) :
    finiteLSCMetric D p = ENNReal.ofReal (D.1 p) := by
  exact D.edist_pt p.1 p.2

theorem finiteLSCMetric_toLSCFun (D : ContMetric) :
    (finiteLSCMetric D).toLSCFun.1 = finiteMetricE D := by
  funext p
  simp only [LSCMetric.toLSCFun, finiteMetricE, finiteLSCMetric_apply]

theorem measurable_finiteLSCMetric : Measurable finiteLSCMetric := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  apply B2.LscTop.measurable_iff_toLSCFun.mpr
  apply B2.LscTop.measurable_of_continuous_apply
  · intro D
    rw [finiteLSCMetric_toLSCFun]
    exact continuous_finiteMetricE D
  · intro p
    have hh : (fun D : ContMetric => ((finiteLSCMetric D).toLSCFun).1 p) =
        fun D => finiteMetricE D p := by
      funext D
      rw [finiteLSCMetric_toLSCFun]
    rw [hh]
    exact measurable_pi_iff.mp measurable_finiteMetricE p

end SupercriticalLQGUniqueness.B2.DG20Lim
