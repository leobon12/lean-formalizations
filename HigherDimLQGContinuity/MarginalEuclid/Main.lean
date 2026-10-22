import HigherDimLQGContinuity.MarginalEuclid.PinTransfer

/-! Lemma 5.1, both pin laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- The marginal Euclidean estimate of Lemma 5.1. -/
theorem marginalEuclid_of {d : ℕ} (hd : 3 ≤ d)
    (hφ : PhiRate d) (hRot : StrongRotLaw d) (hConc : ConcentrationStmt d) :
    MarginalEuclidStmt d := by
  intro R hR p hp r hr hr1
  obtain ⟨ξu, Cu, hξu, hCu, hunit⟩ :=
    marginalEuclid_unit hd hφ hRot hConc hR hp hr hr1
  obtain ⟨ξt, Ct, hξt, hCt, hten⟩ :=
    marginalEuclid_ten hd hφ hRot hConc hR hp hr hr1
  let ξ₁ := min ξu ξt
  let C := max Cu Ct
  have hξ₁ : 0 < ξ₁ := lt_min hξu hξt
  have hC : 0 ≤ C := by dsimp [C]; exact le_max_of_le_left hCu
  refine ⟨ξ₁, C, hξ₁, hC, ?_⟩
  intro ξ hξ D hD s hs
  have hξu' : ξ ∈ Ioc (0 : ℝ) ξu := ⟨hξ.1, (le_min_iff.mp hξ.2).1⟩
  have hξt' : ξ ∈ Ioc (0 : ℝ) ξt := ⟨hξ.1, (le_min_iff.mp hξ.2).2⟩
  have hpow : 0 ≤ ξ ^ (r * p) := (Real.rpow_pos_of_pos hξ.1 _).le
  rcases hs with rfl | rfl
  · rw [pinLaw_one (by omega : 2 ≤ d)]
    calc
      _ ≤ ENNReal.ofReal (Cu * ξ ^ (r * p)) := hunit ξ hξu' D hD
      _ ≤ ENNReal.ofReal (C * ξ ^ (r * p)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
  · calc
      _ ≤ ENNReal.ofReal (Ct * ξ ^ (r * p)) := hten ξ hξt' D hD
      _ ≤ ENNReal.ofReal (C * ξ ^ (r * p)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)

end HigherDimLQGContinuity
