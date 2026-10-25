import SupercriticalLQGUniqueness.B2.PfeAxioms.ContinuousLFPPMeasurable
import LQGMetric.Field.CircleAvgProc

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem wholePlaneGFF_map_ne_dirac
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (a : DistC) :
    P.map h ≠ Measure.dirac a := by
  intro hdirac
  have hae : ∀ᵐ ω ∂P, h ω = a := by
    apply (ae_map_iff hh.measurable.aemeasurable (measurableSet_singleton a)).mp
    rw [hdirac]
    exact (ae_dirac_iff (measurableSet_singleton a)).mpr rfl
  have hc : CircleAvg.cInc h 2 0 1 0 =ᵐ[P]
      (fun _ => circleAvg a 2 0 - circleAvg a 1 0) := by
    filter_upwards [hae] with ω hω
    simp [CircleAvg.cInc, hω]
  have hv := CircleAvg.variance_cInc_one hh (r := 2) (by norm_num) 0
  have hv0 : Var[CircleAvg.cInc h 2 0 1 0; P] = 0 := by
    rw [variance_congr hc]
    simp [variance, evariance]
  rw [hv0] at hv
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_of_pos hlog] at hv
  linarith

end SupercriticalLQGUniqueness.B2.PfeAxioms
