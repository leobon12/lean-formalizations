import SupercriticalLQGUniqueness.B2.PfeAxioms.CanonicalPointCostMeasurable
import LQGMetric.Papers.DFGPS.L2_6Law

 



set_option autoImplicit false
noncomputable section

open MeasureTheory LQGMetric LQGMetric.DFGPS
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem map_canonical_observable_fieldScale
    {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (f : DistC → β) (hf : AEMeasurable f normGFFLaw)
    {r : ℝ} (hr : 0 < r) :
    P.map (fun ω => f (fieldScale r (h ω))) = P.map (fun ω => f (h ω)) := by
  have hOld :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh
  have hLaw : P.map (fun ω => fieldScale r (h ω)) = P.map h :=
    map_fieldScale hOld hr
  have hCan : normGFFLaw = P.map h := normGFFLaw_eq_of_normalized P h hh
  have hf' : AEMeasurable f (P.map h) := by simpa only [← hCan] using hf
  have hfScale : AEMeasurable f (P.map fun ω => fieldScale r (h ω)) := by
    simpa only [hLaw] using hf'
  calc
    P.map (fun ω => f (fieldScale r (h ω))) =
        (P.map fun ω => fieldScale r (h ω)).map f := by
      exact (AEMeasurable.map_map_of_aemeasurable hfScale
        (LQGMetric.DFGPS.isWholePlaneGFF_fieldScale hh.1 hr).measurable.aemeasurable).symm
    _ = (P.map h).map f := by rw [hLaw]
    _ = P.map (fun ω => f (h ω)) :=
      AEMeasurable.map_map_of_aemeasurable hf' hh.1.measurable.aemeasurable

end SupercriticalLQGUniqueness.B2.PfeAxioms
