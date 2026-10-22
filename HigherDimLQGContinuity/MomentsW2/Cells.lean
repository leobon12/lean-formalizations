import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.DGZ.SuperExpAcross
import HigherDimLQGMetric.DGZ.BadBoxTools

/-!
# Uniform fine-cell crossing probabilities for W2

The lower quantile of a unit crossing is controlled uniformly by `UNondegShape` and
`UQuantCompShape`. Scaling the fine band gives the same estimate in every dyadic cell.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ}

/-- A uniform lower tail at the unit shell, normalized by the upper quantile. -/
theorem w2_unit_cross_low (hN : UNondegShape d κ) (hQ : UQuantCompShape d κ)
    {b μ θ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hθ : 0 < θ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 2 1 ≤
            c₀ * DGZ.aQ P H ξ n (3 / 4 : ℝ≥0∞)} ≤ ENNReal.ofReal θ := by
  obtain ⟨δ, hδ, hδbound⟩ := hN b μ hb hμ 0 2 1 (by norm_num) (by norm_num) θ hθ
  obtain ⟨C, hC, hCbound⟩ := hQ b μ hb hμ (3 / 4 : ℝ≥0∞) (2⁻¹ : ℝ≥0∞)
    (by norm_num) (by
      rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num) (by norm_num) (by norm_num)
  refine ⟨δ / C, div_pos hδ hC, ?_⟩
  intro ξ hξ Ω _ P W H hH n
  have hq := hCbound ξ hξ Ω P W H hH n
  have ht : δ / C * DGZ.aQ P H ξ n (3 / 4 : ℝ≥0∞) ≤
      δ * DGZ.aQ P H ξ n 2⁻¹ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]
    calc
      δ * DGZ.aQ P H ξ n (3 / 4 : ℝ≥0∞) ≤ δ * (C * DGZ.aQ P H ξ n 2⁻¹) :=
        mul_le_mul_of_nonneg_left hq hδ.le
      _ = δ * DGZ.aQ P H ξ n 2⁻¹ * C := by ring
  exact (measure_mono (fun ω hω => le_trans hω ht)).trans
    (hδbound ξ hξ Ω P W H hH n)

/-- Every translated fine-band crossing has the same uniform lower-tail bound. -/
theorem w2_cell_cross_low (hκ : IsLFPPKernel κ)
    (hN : UNondegShape d κ) (hQ : UQuantCompShape d κ)
    {b μ θ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hθ : 0 < θ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        DGZ.IsDyadicRealization κ P W H → ∀ m n : ℕ, m ≤ n → ∀ w : Rd d,
          P {ω | DGZ.acrossDist ξ (fun z => H n z ω - H m z ω) w
            (2 * (2 : ℝ)⁻¹ ^ m) ((2 : ℝ)⁻¹ ^ m) ≤
            c₀ * (2 : ℝ)⁻¹ ^ m * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞)} ≤
              ENNReal.ofReal θ := by
  obtain ⟨c₀, hc₀, hunit⟩ := w2_unit_cross_low hN hQ hb hμ hθ
  refine ⟨c₀, hc₀, ?_⟩
  intro ξ hξ Ω _ P W H hH m n hmn w
  have hG := DGZ.isBandVersion_sub_of_realization hκ hH hmn
  have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  have hlaw := DGZ.BadBox.measure_acrossDist_band_le_eq hκ hH hmn hG ξ w 2 1
    (c₀ * (2 : ℝ)⁻¹ ^ m * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞))
  simp only [one_mul] at hlaw
  have hdiv : c₀ * (2 : ℝ)⁻¹ ^ m * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞) /
      (2 : ℝ)⁻¹ ^ m = c₀ * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞) := by
    field_simp
  rw [hdiv] at hlaw
  exact hlaw.le.trans (hunit ξ hξ Ω P W H hH (n - m))

/-- The law of a dyadic crossing does not depend on the shell centre. -/
theorem w2_across_prob_translate (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : DGZ.IsDyadicRealization κ P W H) (ξ : ℝ)
    (n : ℕ) (c : Rd d) (r₁ r₂ t : ℝ) :
    P {ω | DGZ.acrossDist ξ (fun z => H n z ω) c r₁ r₂ ≤ t} =
      P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ ≤ t} := by
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hmap := DGZ.map_acrossDist_translate_eq (hH.band n) (hH.band n)
    hH.whiteNoise hH.whiteNoise hκ ha ξ c 0 r₁ r₂
  simp only [add_zero] at hmap
  exact DGZ.BadBox.measure_le_eq_of_map_eq
    (DGZ.measurable_acrossDist (hH.band n).continuous (hH.band n).measurable ξ c r₁ r₂)
    (DGZ.measurable_acrossDist (hH.band n).continuous (hH.band n).measurable ξ 0 r₁ r₂)
    hmap t

end HigherDimLQGContinuity
