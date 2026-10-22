import HigherDimLQGMetric.Limits.ScaleLimitLaw

/-! Positive scalar multiplication preserves the proper continuous metric support. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- MA5 properness at infinity is invariant under positive constant scaling. -/
theorem l6c_proper_smul {d : ℕ} {D : Rd d × Rd d → ℝ}
    (hD : IsProperFn D) {s : ℝ} (hs : 0 < s) :
    IsProperFn (fun p => s * D p) := by
  intro r hr M
  obtain ⟨R, hrR, hbound⟩ := hD r hr (M / s)
  refine ⟨R, hrR, ?_⟩
  rw [infPairs] at hbound ⊢
  refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
  have hpoint : ENNReal.ofReal (M / s) ≤ ENNReal.ofReal (D (u, v)) :=
    hbound.trans (iInf_le_of_le u (iInf_le_of_le hu
      (iInf_le_of_le v (iInf_le _ hv))))
  calc
    ENNReal.ofReal M = ENNReal.ofReal s * ENNReal.ofReal (M / s) := by
      rw [← ENNReal.ofReal_mul hs.le, mul_div_cancel₀ M hs.ne']
    _ ≤ ENNReal.ofReal s * ENNReal.ofReal (D (u, v)) := by
      gcongr
    _ = ENNReal.ofReal (s * D (u, v)) := (ENNReal.ofReal_mul hs.le).symm

/-- Positive multiples of proper continuous metrics remain proper continuous metrics. -/
theorem l6c_good_smul {d : ℕ} (D : C(Rd d × Rd d, ℝ))
    (hD : IsContinuousMetric D ∧ IsProperFn D)
    {s : ℝ} (hs : 0 < s) :
    IsContinuousMetric (s • D) ∧ IsProperFn (s • D) := by
  constructor
  · exact (ContMetric.smul s hs (⟨D, hD.1⟩ : ContMetric d)).2
  · change IsProperFn (fun p => s * D p)
    exact l6c_proper_smul hD.2 hs

end HigherDimLQGMetric
