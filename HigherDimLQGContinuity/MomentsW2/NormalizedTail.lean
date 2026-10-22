import HigherDimLQGContinuity.MomentsW2.Normalize

/-!
# Normalized shell lower tail at a fixed coarse scale

The CRUDE comparison inserts the factor `2^(b²m/2)`. The bound retains the
coarse-field event and the exact Peierls term for the final scale choice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP
open HigherDimLFPP.DGZ (cbox)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- CRUDE turns the unnormalized crossing estimate into a normalized tail estimate. -/
theorem w2_normalized_tail (hd : 2 ≤ d) (hκ : IsLFPPKernel κ)
    (hCr : CrudeLowerShape d κ) (hN : UNondegShape d κ) (hQ : UQuantCompShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        DGZ.IsDyadicRealization κ P W H →
        ∀ m n : ℕ, m ≤ n → ∀ r₁ r₂ A : ℝ,
          0 ≤ r₂ → r₂ < r₁ → (2 : ℝ)⁻¹ ^ m ≤ 1 / 2 →
          ∀ N D : ℕ, r₁ / ((2 : ℝ)⁻¹ ^ m) ≤ N →
            (D : ℝ) * ((2 : ℝ)⁻¹ ^ m) + 8 * ((2 : ℝ)⁻¹ ^ m) ≤ r₁ - r₂ →
            P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
              DGZ.aQ P H ξ n 2⁻¹ <
                c₀ * (2 : ℝ)⁻¹ ^ m /
                  (4 * Real.exp A * (2 : ℝ) ^ (b ^ 2 * m / 2))} ≤
              P {ω | ∃ z ∈ cbox (0 : Rd d) (r₁ + 1), A < -(ξ * H m z ω)} +
                (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ (D / 2) := by
  obtain ⟨c₀, hc₀, htail⟩ := w2_crossing_lower_tail hd hκ hN hQ hb hμ
  refine ⟨c₀, hc₀, ?_⟩
  intro ξ hξ Ω _ P W H hH m n hmn r₁ r₂ A hr₂ hr hs2 N D hN hD
  have hnorm := w2_normalizer_le hCr hξ hH hmn
  have hmed : 0 < DGZ.aQ P H ξ n 2⁻¹ :=
    DGZ.tight_aQ_pos (by omega : 0 < d) hH ξ n (by norm_num) (by norm_num)
  have hpow : 0 < (2 : ℝ) ^ (b ^ 2 * m / 2) := by positivity
  have hden : 0 < 4 * Real.exp A * (2 : ℝ) ^ (b ^ 2 * m / 2) := by positivity
  have hs : 0 < (2 : ℝ)⁻¹ ^ m := by positivity
  have hsub : {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
      DGZ.aQ P H ξ n 2⁻¹ <
        c₀ * (2 : ℝ)⁻¹ ^ m / (4 * Real.exp A * (2 : ℝ) ^ (b ^ 2 * m / 2))} ⊆
      {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ <
        c₀ * (2 : ℝ)⁻¹ ^ m * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞) /
          Real.exp A} := by
    intro ω hω
    have h1 : DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ <
        (c₀ * (2 : ℝ)⁻¹ ^ m / (4 * Real.exp A * (2 : ℝ) ^ (b ^ 2 * m / 2))) *
          DGZ.aQ P H ξ n 2⁻¹ := (div_lt_iff₀ hmed).1 hω
    have h2 : (c₀ * (2 : ℝ)⁻¹ ^ m / (4 * Real.exp A * (2 : ℝ) ^ (b ^ 2 * m / 2))) *
          DGZ.aQ P H ξ n 2⁻¹ ≤
        (c₀ * (2 : ℝ)⁻¹ ^ m / (4 * Real.exp A * (2 : ℝ) ^ (b ^ 2 * m / 2))) *
          (4 * (2 : ℝ) ^ (b ^ 2 * m / 2) *
            DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞)) :=
      mul_le_mul_of_nonneg_left hnorm (div_nonneg (mul_nonneg hc₀.le hs.le) hden.le)
    have h3 : (c₀ * (2 : ℝ)⁻¹ ^ m / (4 * Real.exp A * (2 : ℝ) ^ (b ^ 2 * m / 2))) *
          (4 * (2 : ℝ) ^ (b ^ 2 * m / 2) *
            DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞)) =
        c₀ * (2 : ℝ)⁻¹ ^ m * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞) /
          Real.exp A := by
      field_simp
    exact lt_of_lt_of_le h1 (h2.trans_eq h3)
  exact (measure_mono hsub).trans (htail ξ hξ Ω P W H hH m n hmn r₁ r₂ A
    hr₂ hr hs2 N D hN hD)

end HigherDimLQGContinuity
