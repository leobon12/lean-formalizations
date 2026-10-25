import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge
import SupercriticalLQGUniqueness.B2.Iface.Statements

set_option autoImplicit false
noncomputable section

open MeasureTheory LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem normGFFLaw_eq_of_normalized
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    normGFFLaw = P.map h :=
  LQGMetric.GM.normGFFLaw_eq
    (SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh)

end SupercriticalLQGUniqueness.B2.PfeAxioms
