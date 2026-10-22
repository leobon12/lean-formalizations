import HigherDimLQGContinuity.Core.Interfaces

/-!
# Four-part event budget for the upper improvement event
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory

/-- References, comparison failure, geometric failure, and the finite
catalogue union each receive one quarter of the target probability. -/
theorem q11_hup_event_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {A R G S B : Set Ω} {pt : ℝ} (hpt : 0 ≤ pt)
    (hsub : A ⊆ Rᶜ ∪ Gᶜ ∪ Sᶜ ∪ B)
    (hR : μ Rᶜ ≤ ENNReal.ofReal (pt / 4))
    (hG : μ Gᶜ ≤ ENNReal.ofReal (pt / 4))
    (hS : μ Sᶜ ≤ ENNReal.ofReal (pt / 4))
    (hB : μ B ≤ ENNReal.ofReal (pt / 4)) :
    μ A ≤ ENNReal.ofReal pt := by
  calc
    μ A ≤ μ (Rᶜ ∪ Gᶜ ∪ Sᶜ ∪ B) := measure_mono hsub
    _ ≤ μ Rᶜ + μ Gᶜ + μ Sᶜ + μ B := by
      have h1 := measure_union_le (μ := μ) Rᶜ Gᶜ
      have h2 := measure_union_le (μ := μ) (Rᶜ ∪ Gᶜ) Sᶜ
      have h3 := measure_union_le (μ := μ) (Rᶜ ∪ Gᶜ ∪ Sᶜ) B
      calc
        μ (Rᶜ ∪ Gᶜ ∪ Sᶜ ∪ B)
            ≤ μ (Rᶜ ∪ Gᶜ ∪ Sᶜ) + μ B := h3
        _ ≤ (μ (Rᶜ ∪ Gᶜ) + μ Sᶜ) + μ B := by gcongr
        _ ≤ (μ Rᶜ + μ Gᶜ) + μ Sᶜ + μ B := by gcongr
    _ ≤ ENNReal.ofReal (pt / 4) + ENNReal.ofReal (pt / 4) +
        ENNReal.ofReal (pt / 4) + ENNReal.ofReal (pt / 4) := by
      exact add_le_add (add_le_add (add_le_add hR hG) hS) hB
    _ = ENNReal.ofReal pt := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end HigherDimLQGContinuity
