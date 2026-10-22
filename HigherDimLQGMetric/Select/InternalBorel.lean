import HigherDimLQGMetric.Select.Internal
import HigherDimLQGMetric.Select.MetricBorel

/-!
# Internal metrics as ambient Borel functions

The countable chain formula extends from the Borel subtype of continuous metrics to the
whole space of continuous two-point functions. Its restriction to length metrics is the
internal distance, giving a directly composable Borel function for configuration events.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- SF2 (MA1 A11): the internal distance on continuous length metrics is the restriction
of a Borel function of the ambient continuous two-point function and its endpoints. -/
theorem measurable_internal_ambient {V : Set (Rd d)} (hV : IsOpen V) :
    ∃ F : C(Rd d × Rd d, ℝ) × Rd d × Rd d → ℝ≥0∞, Measurable F ∧
      ∀ D : ContMetric d, D.IsLength → ∀ x y : Rd d,
        D.internal V x y = F (D.1, x, y) := by
  have hEmb : MeasurableEmbedding
      (fun p : ContMetric d × Rd d × Rd d =>
        ((p.1.1, p.2) : C(Rd d × Rd d, ℝ) × Rd d × Rd d)) := by
    exact (MeasurableEmbedding.subtype_coe (measurableSet_isContinuousMetric_select d)).prodMap
      MeasurableEmbedding.id
  obtain ⟨F, hFm, hF⟩ := hEmb.exists_measurable_extend
    (ContMetric.measurable_chainInf V) (fun _ => inferInstance)
  refine ⟨F, hFm, ?_⟩
  intro D hD x y
  rw [D.internal_eq_chainInf hD hV]
  have h := congrFun hF (D, x, y)
  exact h.symm

end HigherDimLQGMetric
