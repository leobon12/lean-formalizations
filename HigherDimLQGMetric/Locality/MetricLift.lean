import HigherDimLQGMetric.Limits.InternalMap

/-! A total metric-valued version of an ambient continuous-map coordinate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

def l7a_metricLift {d : ℕ} (E : C(Rd d × Rd d, ℝ)) : ContMetric d := by
  classical
  exact if h : IsContinuousMetric E then ⟨E, h⟩
    else fieldLfppMetric 0 (0 : C(Rd d, ℝ))

theorem l7a_metricLift_val {d : ℕ} {E : C(Rd d × Rd d, ℝ)}
    (hE : IsContinuousMetric E) : (l7a_metricLift E).1 = E := by
  classical
  simp [l7a_metricLift, hE]

theorem l7a_metricLift_isLength {d : ℕ} {E : C(Rd d × Rd d, ℝ)}
    (hE : IsContLengthFn E) : (l7a_metricLift E).IsLength := by
  have hEq : l7a_metricLift E = (⟨E, hE.1⟩ : ContMetric d) :=
    Subtype.ext (l7a_metricLift_val hE.1)
  rw [hEq]
  exact hE.2

theorem l7a_measurable_metricLift {d : ℕ} :
    Measurable (l7a_metricLift (d := d)) := by
  classical
  have hEmb : MeasurableEmbedding
      ((↑) : ContMetric d → C(Rd d × Rd d, ℝ)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_isContinuousMetric_select d)
  apply (hEmb.measurable_comp_iff).mp
  have heq : ((↑) : ContMetric d → C(Rd d × Rd d, ℝ)) ∘ l7a_metricLift =
      (fun X => if h : IsContinuousMetric X then X
        else (fieldLfppMetric 0 (0 : C(Rd d, ℝ))).1) := by
    funext X
    simp only [Function.comp_def, l7a_metricLift]
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite (measurableSet_isContinuousMetric_select d)
    measurable_id measurable_const

end HigherDimLQGMetric
