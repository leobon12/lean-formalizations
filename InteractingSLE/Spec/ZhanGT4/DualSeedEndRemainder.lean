/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndClock

/-!
# The remainder on the translated original grid

Packet PROVE-ZHAN-GT4-A22. Translate original-clock cells by `ε`, rather
than identifying original and restarted dyadic grids. The checked common
tube modulus controls the resulting arbitrary short cells.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

/-- Actual restarted field remainders on the original-clock cells. -/
def seedEndRemainder (ψ φ : ℝ → ℝ → ℝ) (β : ℝ → ℝ) (ε τ t : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (cells n),
    if ε ≤ min (grid n k) t ∧ min (grid n k) t < ε + τ ∧ min (grid n (k + 1)) t ≤ ε + τ then
      Ito.fieldStepRem ψ φ β (min (grid n k) t - ε : ℝ≥0) (min (grid n (k + 1)) t - ε : ℝ≥0)
    else 0

/-- These remainders are nonnegative, including repeated grid points. -/
theorem seedEndRemainder_nonneg (ψ φ : ℝ → ℝ → ℝ) (β : ℝ → ℝ) (ε τ t : ℝ≥0) (n : ℕ) :
    0 ≤ seedEndRemainder ψ φ β ε τ t n := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact Ito.fieldStepRem_nonneg (show
      ((min (grid n k) t - ε : ℝ≥0) : ℝ) ≤ (min (grid n (k + 1)) t - ε : ℝ≥0) from
      tsub_le_tsub_right (min_le_min_right t (grid_mono n (Nat.le_succ k))) ε)
  · exact le_rfl

/-- Translation of the grid does not affect the vanishing tube remainder. -/
theorem tendsto_seedEndRemainder {ψ φ : ℝ → ℝ → ℝ} {β : ℝ → ℝ}
    (ε τ t : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ)
    (hβ : ContinuousOn β (Icc 0 (τ : ℝ)))
    (hψ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (seedPathTube β 0 τ (3 * ρ)))
    (hφ : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (seedPathTube β 0 τ (3 * ρ))) :
    Tendsto (seedEndRemainder ψ φ β ε τ t) atTop (𝓝 0) := by
  have hmesh : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  apply Metric.tendsto_nhds.2
  intro η hη
  let v : ℝ := η / (t + 1)
  have hv : 0 < v := div_pos hη (by positivity)
  obtain ⟨δ, hδ, hrem⟩ := exists_seed_tube_stepRem_le hρ hβ hψ hφ hv
  filter_upwards [hmesh.eventually_lt_const hδ] with n hn
  let p : ℕ → ℝ≥0 := fun k => min (grid n k) t
  have hp : Monotone p := fun k j hkj => min_le_min_right t (grid_mono n hkj)
  have hb : seedEndRemainder ψ φ β ε τ t n ≤ v * t := by
    calc _ ≤ ∑ k ∈ Finset.range (cells n), v * ((p (k + 1) : ℝ) - p k) := by
          apply Finset.sum_le_sum
          intro k _
          split_ifs with hh
          · have he₁ : ε ≤ p k := hh.1
            have he₂ : ε ≤ p (k + 1) := he₁.trans (hp (Nat.le_succ k))
            have hlen : ((p (k + 1) - ε : ℝ≥0) : ℝ) - (p k - ε : ℝ≥0) =
                (p (k + 1) : ℝ) - p k := by
              rw [NNReal.coe_sub he₂, NNReal.coe_sub he₁]
              ring
            rw [← hlen]
            apply hrem
            · exact (p k - ε).coe_nonneg
            · exact tsub_le_tsub_right (hp (Nat.le_succ k)) ε
            · exact (tsub_le_iff_left.2 hh.2.2 : p (k + 1) - ε ≤ τ)
            · rw [hlen]
              exact (seed_grid_sub_le n k t).trans_lt hn
          · exact mul_nonneg hv.le (sub_nonneg.2 (show (p k : ℝ) ≤ p (k + 1) from hp (Nat.le_succ k)))
      _ = v * ((p (cells n) : ℝ) - p 0) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_range_sub (fun k => (p k : ℝ)) (cells n)
      _ ≤ v * t := by
          simp only [p, grid_zero, zero_min, NNReal.coe_zero, sub_zero]
          exact mul_le_mul_of_nonneg_left (show (min (grid n (cells n)) t : ℝ) ≤ t from min_le_right _ _) hv.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (seedEndRemainder_nonneg ψ φ β ε τ t n)]
  apply hb.trans_lt
  have he : v * (t + 1) = η := div_mul_cancel₀ _ (by positivity : (t : ℝ) + 1 ≠ 0)
  nlinarith only [he, hv]

end InteractingSLE.ZhanGT4
