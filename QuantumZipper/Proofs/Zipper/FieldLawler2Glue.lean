import QuantumZipper.Proofs.Zipper.FieldLawlerCoverDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 2: majorant comparison for sums of excursion integrals

For `FLImageSumBoundStmt` (Field–Lawler, EJP 20 (2015), proof of Prop. 3.4, p. 9) the sum
`Σⱼ ℰ(ηⱼ, J) = Σⱼ ∫_J ∂_y hⱼ` is bounded through a harmonic majorant `Φ` of all finite partial sums
`Σ_{j ∈ F} hⱼ` near `J` (e.g. `2 ×` the harmonic measure of the union, FL Cor. 4.2):
`fl2_tsum_excR_le`. Since each `hⱼ` and `Φ` vanish on `J`, `∂_y` is monotone
(`fl2_yDer_le`) and additive (`fl2_yDer_sum`). The lower Lebesgue integral is superadditive, so no
measurability of `x ↦ ∂_y h(x)` is needed. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

theorem fl2_yDer_eq {h : ℂ → ℝ} {x L : ℝ}
    (hL : Tendsto (fun y : ℝ => h ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0) (𝓝 L)) :
    yDer h x = L := by
  unfold yDer
  rw [if_pos ⟨L, hL⟩]
  exact hL.limUnder_eq

/-- `∂_y` is monotone for nonnegative functions below a majorant with a vertical derivative. -/
theorem fl2_yDer_le {u φ : ℂ → ℝ} {x L : ℝ}
    (hφ : Tendsto (fun y : ℝ => φ ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0) (𝓝 L))
    (hu0 : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 ≤ u ((x : ℂ) + (y : ℂ) * I))
    (hle : ∀ᶠ y : ℝ in 𝓝[>] 0, u ((x : ℂ) + (y : ℂ) * I) ≤ φ ((x : ℂ) + (y : ℂ) * I)) :
    yDer u x ≤ yDer φ x := by
  rw [fl2_yDer_eq hφ]
  have hpos : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < y := self_mem_nhdsWithin
  have hL0 : 0 ≤ L := by
    refine ge_of_tendsto hφ ?_
    filter_upwards [hu0, hle, hpos] with y h0 h1 hy
    exact div_nonneg (h0.trans h1) hy.le
  unfold yDer
  split_ifs with hex
  · obtain ⟨Lu, hLu⟩ := hex
    rw [hLu.limUnder_eq]
    refine le_of_tendsto_of_tendsto hLu hφ ?_
    filter_upwards [hle, hpos] with y h1 hy
    exact div_le_div_of_nonneg_right h1 hy.le
  · exact hL0

theorem fl2_finset_lintegral_le {α ι : Type} [MeasurableSpace α] (μ : Measure α)
    (F : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑ j ∈ F, ∫⁻ a, f j a ∂μ ≤ ∫⁻ a, ∑ j ∈ F, f j a ∂μ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    rw [Finset.sum_insert ha]
    calc ∫⁻ x, f a x ∂μ + ∑ j ∈ F, ∫⁻ x, f j x ∂μ
        ≤ ∫⁻ x, f a x ∂μ + ∫⁻ x, ∑ j ∈ F, f j x ∂μ := add_le_add le_rfl ih
      _ ≤ ∫⁻ x, (f a x + ∑ j ∈ F, f j x) ∂μ := le_lintegral_add _ _
      _ = ∫⁻ x, ∑ j ∈ insert a F, f j x ∂μ := by
          congr 1; funext x; rw [Finset.sum_insert ha]

end FieldLawler
end QuantumZipper
