import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.LoopCover




 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events

 
theorem jointEval_lsc :
    LowerSemicontinuous (fun p : LSCMetric × (ℂ × ℂ) => p.1 p.2) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hG
  have hq : Tendsto (fun n => (G n).2) atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hG
  exact (LSCMetric.tendsto_iff.mp hm).1 (fun n => (G n).2) p.2 hq

 
theorem jointEval_borel :
    @Measurable (LSCMetric × (ℂ × ℂ)) ENNReal (borel _) inferInstance
      (fun p => p.1 p.2) := by
  letI : MeasurableSpace (LSCMetric × (ℂ × ℂ)) := borel _
  letI : OpensMeasurableSpace (LSCMetric × (ℂ × ℂ)) := ⟨le_rfl⟩
  exact jointEval_lsc.measurable

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events
