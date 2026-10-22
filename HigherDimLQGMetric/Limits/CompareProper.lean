import HigherDimLQGMetric.Limits.RandomCompareTight
import HigherDimLQGMetric.Limits.ScaleProper

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Topology Filter
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- MA5 properness at infinity transfers through any positive global lower
comparison of continuous metric functions. -/
theorem l6c_proper_of_lower {d : ℕ}
    {A B : C(Rd d × Rd d, ℝ)} (hA : IsProperFn A)
    {c : ℝ} (hc : 0 < c)
    (hAB : ∀ p : Rd d × Rd d, c * A p ≤ B p) : IsProperFn B := by
  intro r hr M
  obtain ⟨R, hrR, hbound⟩ := hA r hr (M / c)
  refine ⟨R, hrR, ?_⟩
  rw [infPairs] at hbound ⊢
  refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
  have hpoint : ENNReal.ofReal (M / c) ≤ ENNReal.ofReal (A (u,v)) :=
    hbound.trans (iInf_le_of_le u (iInf_le_of_le hu
      (iInf_le_of_le v (iInf_le _ hv))))
  calc
    ENNReal.ofReal M = ENNReal.ofReal c * ENNReal.ofReal (M / c) := by
      rw [← ENNReal.ofReal_mul hc.le, mul_div_cancel₀ M hc.ne']
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (A (u,v)) := by gcongr
    _ = ENNReal.ofReal (c * A (u,v)) := (ENNReal.ofReal_mul hc.le).symm
    _ ≤ ENNReal.ofReal (B (u,v)) := ENNReal.ofReal_le_ofReal (hAB (u,v))

/-- A pseudo metric comparable on both sides to a genuine proper metric is
itself a genuine proper metric. -/
theorem l6c_good_of_compare {d : ℕ}
    {A B : C(Rd d × Rd d, ℝ)}
    (hA : IsContinuousMetric A ∧ IsProperFn A)
    (hB : B ∈ metricAlgSet_select)
    {c C : ℝ} (hc : 0 < c) (_hC : 0 ≤ C)
    (hcmp : ∀ p : Rd d × Rd d, c * A p ≤ B p ∧ B p ≤ C * A p) :
    IsContinuousMetric B ∧ IsProperFn B := by
  have hBmet : IsContinuousMetric B :=
    s8a_envelope_isContinuousMetric
      (K := {A}) (fun _ h => by simpa only [mem_singleton_iff] using h ▸ hA.1)
      hc ⟨hB, A, mem_singleton A, hcmp⟩
  exact ⟨hBmet, l6c_proper_of_lower hA.2 hc (fun p => (hcmp p).1)⟩

end HigherDimLQGMetric
