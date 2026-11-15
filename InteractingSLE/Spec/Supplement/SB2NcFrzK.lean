/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcClockP

/-!
# Random closed sets observed through dyadic hits are frozen

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B). A closed set is determined by the closed dyadic squares it
meets (`subset_of_dyadicHits`). So a random closed set whose dyadic-hit events are events of the completion
`aeSigma 𝒢 P` is frozen under the conditional laws given `𝒢` (**`ae_ae_eq_of_dyadicHit`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nc

open Restart LocalSets

/-- **A closed set is determined by the dyadic squares it meets.** -/
theorem subset_of_dyadicHits {A B : Set ℂ} (hB : IsClosed B)
    (h : ∀ (n : ℕ) (k : ℤ × ℤ), (dyadicSquare n k ∩ A).Nonempty → (dyadicSquare n k ∩ B).Nonempty) : A ⊆ B := by
  intro z hz
  refine hB.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨w, hw1, hw2⟩ := h n (dyadicIndexOf n z) ⟨z, mem_dyadicSquare_indexOf n z, hz⟩
  refine ⟨w, hw2, ?_⟩
  rw [dist_eq_norm]
  have h2 : (2 : ℝ) / 2 ^ n = 2 * (1 / 2) ^ n := by rw [one_div_pow]; ring
  calc ‖z - w‖ ≤ 2 / 2 ^ n := norm_sub_le_of_mem_dyadicSquare (mem_dyadicSquare_indexOf n z) hw1
    _ = 2 * (1 / 2) ^ n := h2
    _ < 2 * (ε / 2) := by linarith
    _ = ε := by ring

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **A random closed set observed through dyadic hits in the completion is frozen.** -/
theorem ae_ae_eq_of_dyadicHit (h𝒢 : 𝒢 ≤ mΩ) {K : Ω → Set ℂ}
    (hK : ∀ (n : ℕ) (k : ℤ × ℤ), MeasurableSet[aeSigma 𝒢 P] {ω | (dyadicSquare n k ∩ K ω).Nonempty})
    (hKc : ∀ ω, IsClosed (K ω)) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), K ω = K ω₀ := by
  have h1 : ∀ᵐ ω₀ ∂P, ∀ (n : ℕ) (k : ℤ × ℤ), ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      ((dyadicSquare n k ∩ K ω).Nonempty ↔ (dyadicSquare n k ∩ K ω₀).Nonempty) := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro k
    exact ae_ae_mem_iff_of_aeSigma (P := P) h𝒢 (hK n k)
  filter_upwards [h1] with ω₀ h
  have h2 : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ (n : ℕ) (k : ℤ × ℤ),
      ((dyadicSquare n k ∩ K ω).Nonempty ↔ (dyadicSquare n k ∩ K ω₀).Nonempty) := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; exact h n
  filter_upwards [h2] with ω hω
  exact Subset.antisymm (subset_of_dyadicHits (hKc ω₀) fun n k hn => (hω n k).1 hn)
    (subset_of_dyadicHits (hKc ω) fun n k hn => (hω n k).2 hn)

end InteractingSLE.Theorem14.SB.Nc
