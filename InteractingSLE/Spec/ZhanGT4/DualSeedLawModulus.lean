/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLawIto

/-!
# Pathwise moduli for the random-field Itô engine

Packet PROVE-ZHAN-GT4-A22. Reuse `Ito.exists_fieldStepRem_le` on the
clamped dyadic grid. The modulus tends to zero on every continuous path;
no differentiability of the Brownian path is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

/-- Sum of the time-field Taylor remainders on the clamped dyadic grid. -/
def seedFieldRemainder (ψ φ : ℝ → ℝ → ℝ) (β : ℝ → ℝ) (n : ℕ) (t : ℝ≥0) : ℝ :=
  ∑ k ∈ Finset.range (cells n),
    Ito.fieldStepRem ψ φ β (min (grid n k) t) (min (grid n (k + 1)) t)

/-- A bound proportional to cell length sums to the same bound times `t`. -/
theorem seedFieldRemainder_le {ψ φ : ℝ → ℝ → ℝ} {β : ℝ → ℝ}
    (n : ℕ) (t : ℝ≥0) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ k ∈ Finset.range (cells n),
      Ito.fieldStepRem ψ φ β (min (grid n k) t) (min (grid n (k + 1)) t) ≤
        η * (((min (grid n (k + 1)) t : ℝ≥0) : ℝ) - min (grid n k) t)) :
    seedFieldRemainder ψ φ β n t ≤ η * t := by
  calc _ ≤ ∑ k ∈ Finset.range (cells n),
        η * (((min (grid n (k + 1)) t : ℝ≥0) : ℝ) - min (grid n k) t) := Finset.sum_le_sum h
    _ = η * (((min (grid n (cells n)) t : ℝ≥0) : ℝ) - min (grid n 0) t) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_range_sub (fun k => ((min (grid n k) t : ℝ≥0) : ℝ)) (cells n)
    _ ≤ _ := by
      simp only [grid_zero, zero_min, NNReal.coe_zero, sub_zero]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right (grid n (cells n)) t) hη

/-- The summed time-field modulus vanishes pathwise. -/
theorem tendsto_seedFieldRemainder {ψ φ : ℝ → ℝ → ℝ} {β : ℝ → ℝ} (t : ℝ≥0)
    (hψ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (Icc 0 (t : ℝ) ×ˢ univ))
    (hφ : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (Icc 0 (t : ℝ) ×ˢ univ))
    (hβ : ContinuousOn β (Icc 0 (t : ℝ))) :
    Tendsto (fun n => seedFieldRemainder ψ φ β n t) atTop (𝓝 0) := by
  have hmesh : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η : ℝ := ε / (t + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hsmall⟩ := Ito.exists_fieldStepRem_le hψ hφ hβ hη
  filter_upwards [hmesh.eventually_lt_const hδ] with n hn
  have hnn : 0 ≤ seedFieldRemainder ψ φ β n t := Finset.sum_nonneg fun k _ =>
    Ito.fieldStepRem_nonneg (by exact_mod_cast min_le_min_right t (grid_mono n (Nat.le_succ k)))
  have hbound : seedFieldRemainder ψ φ β n t ≤ η * t := by
    apply seedFieldRemainder_le n t hη.le
    intro k _
    apply hsmall
    · exact (min (grid n k) t).coe_nonneg
    · exact_mod_cast min_le_min_right t (grid_mono n (Nat.le_succ k))
    · exact_mod_cast min_le_right (grid n (k + 1)) t
    · have hg : ((min (grid n (k + 1)) t : ℝ≥0) : ℝ) - min (grid n k) t ≤ 1 / 2 ^ n := by
        simpa only [NNReal.coe_min] using seed_grid_sub_le n k t
      exact hg.trans_lt hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  refine hbound.trans_lt ?_
  have he : η * (t + 1) = ε := div_mul_cancel₀ _ (by positivity : (t : ℝ) + 1 ≠ 0)
  nlinarith

end InteractingSLE.ZhanGT4
