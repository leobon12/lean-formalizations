import HigherDimLQGMetric.Amplify.FiniteProb

/-! Converting three finite-union failure estimates into a probability lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P]

/-- A measurable union of failures of total probability at most `1-p`
leaves probability at least `p` for every event containing its complement. -/
theorem amplify_good_of_three_errors
    (B₁ B₂ B₃ Good : Set Ω)
    (hB₁ : NullMeasurableSet B₁ P)
    (hB₂ : NullMeasurableSet B₂ P)
    (hB₃ : NullMeasurableSet B₃ P)
    {e₁ e₂ e₃ p : ℝ}
    (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (he₃ : 0 ≤ e₃)
    (_hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsmall : e₁ + e₂ + e₃ ≤ 1 - p)
    (h₁ : P B₁ ≤ ENNReal.ofReal e₁)
    (h₂ : P B₂ ≤ ENNReal.ofReal e₂)
    (h₃ : P B₃ ≤ ENNReal.ofReal e₃)
    (hGood : ∀ᵐ ω ∂P, ω ∈ (B₁ ∪ B₂ ∪ B₃)ᶜ → ω ∈ Good) :
    ENNReal.ofReal p ≤ P Good := by
  let B := B₁ ∪ B₂ ∪ B₃
  have hB : NullMeasurableSet B P := (hB₁.union hB₂).union hB₃
  have hmeasure : P B ≤ ENNReal.ofReal (1 - p) := by
    calc
      P B ≤ P (B₁ ∪ B₂) + P B₃ := measure_union_le _ _
      _ ≤ (P B₁ + P B₂) + P B₃ := add_le_add (measure_union_le _ _) le_rfl
      _ ≤ ENNReal.ofReal e₁ + ENNReal.ofReal e₂ + ENNReal.ofReal e₃ := by gcongr
      _ = ENNReal.ofReal (e₁ + e₂ + e₃) := by
        rw [← ENNReal.ofReal_add he₁ he₂,
          ← ENNReal.ofReal_add (add_nonneg he₁ he₂) he₃]
      _ ≤ ENNReal.ofReal (1 - p) := ENNReal.ofReal_le_ofReal hsmall
  have hsub : ENNReal.ofReal p = 1 - ENNReal.ofReal (1 - p) := by
    have hqp : 0 ≤ 1 - p := by linarith
    calc
      ENNReal.ofReal p = ENNReal.ofReal (1 - (1 - p)) := by congr 1; ring
      _ = ENNReal.ofReal 1 - ENNReal.ofReal (1 - p) := ENNReal.ofReal_sub 1 hqp
      _ = _ := by norm_num
  calc
    ENNReal.ofReal p = 1 - ENNReal.ofReal (1 - p) := hsub
    _ ≤ 1 - P B := tsub_le_tsub_left hmeasure 1
    _ = P Bᶜ := by rw [measure_compl₀ hB (measure_ne_top P B), measure_univ]
    _ ≤ P Good := measure_mono_ae hGood

end HigherDimLQGMetric
