import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedLaw
import SupercriticalLQGUniqueness.Exponent.HeatVersion

set_option autoImplicit false
noncomputable section

open MeasureTheory LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem normalized_canonical_model :
    IsProbabilityMeasure normGFFLaw ∧
      IsNormalizedWholePlaneGFF (id : DistC → DistC) normGFFLaw := by
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := exists_normalizedGFF
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  have hLaw := normGFFLaw_eq_of_normalized P h hh
  rw [hLaw]
  have hOld :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh
  have hProb : IsProbabilityMeasure (P.map h) :=
    (Measure.isProbabilityMeasure_map_iff hh.1.measurable.aemeasurable).2 inferInstance
  have hNormOld : IsNormalizedWPGFF (id : DistC → DistC) (P.map h) := by
    refine ⟨LQGMetric.GM.isWholePlaneGFF_id_map hh.1, ?_⟩
    exact (ae_map_iff hh.1.measurable.aemeasurable
      (measurableSet_eq_fun (LQGMetric.measurable_circleAvg_left 1 0) measurable_const)).2
        hOld.2
  exact ⟨hProb,
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalized_new_of_old hNormOld⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
