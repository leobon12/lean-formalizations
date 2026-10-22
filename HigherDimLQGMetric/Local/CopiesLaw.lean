import HigherDimLQGMetric.Local.CopiesCI
import HigherDimLQGMetric.Select.MetricBorel
import LQGMetric.Prob.CondCopies

/-!
# Conditionally independent copies of a continuous metric

The underlying probability space is the original space times `ContMetric d`; the second
coordinate is sampled from the regular conditional law given the field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

/-- The canonical conditional-copy extension for a measurable field and a measurable
continuous metric. Both field-metric pairs have the original law. -/
theorem l7b_conditional_copies {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (Dh : Ω → ContMetric d) (hh : Measurable h) (hD : Measurable Dh) :
    ∃ ν : Measure (Ω × ContMetric d), IsProbabilityMeasure ν ∧
      ν.map (fun p => (h p.1, Dh p.1)) = P.map (fun ω => (h ω, Dh ω)) ∧
      ν.map (fun p => (h p.1, p.2)) = P.map (fun ω => (h ω, Dh ω)) ∧
      LQGMetric.CondIndepEv
        (fullSigmaRd (fun p : Ω × ContMetric d => h p.1))
        (MeasurableSpace.comap (fun p : Ω × ContMetric d => Dh p.1) inferInstance)
        (MeasurableSpace.comap (Prod.snd : Ω × ContMetric d → ContMetric d) inferInstance) ν := by
  have hΩ : Nonempty Ω := ⟨(nonempty_of_measure_ne_zero
    (show P (Set.univ : Set Ω) ≠ 0 by simp)).choose⟩
  haveI : Nonempty (ContMetric d) := ⟨Dh (Classical.choice hΩ)⟩
  let ν := LQGMetric.condCopyMeasure Dh h P hh
  refine ⟨ν, inferInstance, ?_, ?_, ?_⟩
  · rw [← LQGMetric.condCopyMeasure_fst (Y := Dh) (X := h) (μ := P) hh,
      Measure.map_map]
    · rfl
    · exact hh.prodMk hD
    · exact measurable_fst
  · exact LQGMetric.condCopyMeasure_map_snd hh hD
  · exact LQGMetric.condIndepEv_condCopy hh hD

end HigherDimLQGMetric
