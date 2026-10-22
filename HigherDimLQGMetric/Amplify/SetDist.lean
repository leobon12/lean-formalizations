import HigherDimLQGMetric.Core.Defs

/-! Comparison of set distances from a pointwise comparison of internal distances. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- An upper comparison of internal distances passes through both infima in
`setDistIn`. -/
theorem amplify_setDistIn_le_mul (D E : ContMetric d)
    (V A B : Set (Rd d)) {C : ℝ} (hC : 0 < C)
    (h : ∀ u ∈ A, ∀ v ∈ B,
      E.internal V u v ≤ ENNReal.ofReal C * D.internal V u v) :
    setDistIn E V A B ≤ ENNReal.ofReal C * setDistIn D V A B := by
  unfold setDistIn
  simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hC).ne'
    ENNReal.ofReal_ne_top]
  exact iInf_mono fun u => iInf_mono fun hu =>
    iInf_mono fun v => iInf_mono fun hv => h u hu v hv

/-- The corresponding lower comparison. -/
theorem amplify_mul_setDistIn_le (D E : ContMetric d)
    (V A B : Set (Rd d)) {C : ℝ} (hC : 0 < C)
    (h : ∀ u ∈ A, ∀ v ∈ B,
      ENNReal.ofReal C * D.internal V u v ≤ E.internal V u v) :
    ENNReal.ofReal C * setDistIn D V A B ≤ setDistIn E V A B := by
  unfold setDistIn
  simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hC).ne'
    ENNReal.ofReal_ne_top]
  exact iInf_mono fun u => iInf_mono fun hu =>
    iInf_mono fun v => iInf_mono fun hv => h u hu v hv

/-- Enlarging the target set can only decrease its internal set distance. -/
theorem amplify_setDistIn_anti_right (D : ContMetric d)
    (V A : Set (Rd d)) {B B' : Set (Rd d)} (hBB' : B ⊆ B') :
    setDistIn D V A B' ≤ setDistIn D V A B := by
  unfold setDistIn
  refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
  exact iInf_le_of_le u (iInf_le_of_le hu
    (iInf_le_of_le v (iInf_le_of_le (hBB' hv) le_rfl)))

end HigherDimLQGMetric
