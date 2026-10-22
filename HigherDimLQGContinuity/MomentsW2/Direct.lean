import HigherDimLQGContinuity.MomentsW2.NormalizedTail

/-!
# Direct cutoff lower tail for W2

At fixed depth, every shell crossing has at least its Euclidean width times the
minimum exponential weight. CRUDE at `m=n` bounds the normalizer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The direct lower tail uses only the coarse field at the full cutoff. -/
theorem w2_direct_tail (hκ : IsLFPPKernel κ) (hCr : CrudeLowerShape d κ)
    {b μ ξ : ℝ} (hξ : UHyp d κ b μ ξ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : DGZ.IsDyadicRealization κ P W H)
    {r₁ r₂ : ℝ} (hr₂ : 0 ≤ r₂) (hr : r₂ < r₁) (n : ℕ) (t : ℝ) :
    P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
      DGZ.aQ P H ξ n 2⁻¹ <
        (r₁ - r₂) * Real.exp (-t) / (4 * (2 : ℝ) ^ (b ^ 2 * n / 2))} ≤
      P {ω | ∃ z ∈ cbox (0 : Rd d) r₁, t < -(ξ * H n z ω)} := by
  have hnorm := w2_normalizer_direct hκ hCr hξ hH n
  have hmed : 0 < DGZ.aQ P H ξ n 2⁻¹ :=
    DGZ.tight_aQ_pos (by have := hξ.base.dim; omega : 0 < d)
      hH ξ n (by norm_num) (by norm_num)
  have hden : 0 < 4 * (2 : ℝ) ^ (b ^ 2 * n / 2) := by positivity
  apply measure_mono
  intro ω hω
  by_contra hno
  simp only [mem_ofPred_eq, not_exists, not_and, not_lt] at hno
  have hlow := DGZ.exp_mul_le_acrossDist (ξ := ξ) (c := (0 : Rd d))
    (by have := hξ.base.dim; omega : 0 < d)
    ((hH.band n).continuous ω) hr₂ hr (m := -t) (by
      intro z hz
      have hz' : z ∈ cbox (0 : Rd d) r₁ := hz.1
      have hh := hno z hz'
      linarith)
  have hlow' : (r₁ - r₂) * Real.exp (-t) ≤
      DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ := by
    simpa only [mul_comm] using hlow
  have hratio : (r₁ - r₂) * Real.exp (-t) /
      (4 * (2 : ℝ) ^ (b ^ 2 * n / 2)) ≤
        DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
          DGZ.aQ P H ξ n 2⁻¹ := by
    apply (div_le_div_iff₀ hden hmed).2
    have hnum : 0 ≤ (r₁ - r₂) * Real.exp (-t) := by positivity
    exact (mul_le_mul_of_nonneg_left hnorm hnum).trans
      (mul_le_mul_of_nonneg_right hlow' hden.le)
  exact (not_lt_of_ge hratio) hω

end HigherDimLQGContinuity
