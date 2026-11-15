/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandTube

/-!
# The summed moving-tube remainder vanishes

Packet PROVE-ZHAN-GT4-A22. The same modulus controls all cells before a
path's stopping horizon. No choice of a finite spatial cover, measurable
Taylor constants, or global domination of the modulus is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

/-- Sum of the actual field remainders on the cells before the horizon. -/
def seedBandRemainder (ψ φ : ℝ → ℝ → ℝ) (β : ℝ → ℝ) (τ t : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (cells n),
    if min (grid n k) t < τ ∧ min (grid n (k + 1)) t ≤ τ then
      Ito.fieldStepRem ψ φ β (min (grid n k) t) (min (grid n (k + 1)) t) else 0

/-- The remainder sum is nonnegative, including degenerate clamped cells. -/
theorem seedBandRemainder_nonneg (ψ φ : ℝ → ℝ → ℝ) (β : ℝ → ℝ) (τ t : ℝ≥0) (n : ℕ) :
    0 ≤ seedBandRemainder ψ φ β τ t n := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact Ito.fieldStepRem_nonneg (by exact_mod_cast min_le_min_right t (grid_mono n (Nat.le_succ k)))
  · exact le_rfl

/-- The actual remainders vanish on every continuous path on its stopped
moving tube. This supplies a simultaneous modulus for all spatial pieces. -/
theorem tendsto_seedBandRemainder {ψ φ : ℝ → ℝ → ℝ} {β : ℝ → ℝ}
    (τ t : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ)
    (hβ : ContinuousOn β (Icc 0 (τ : ℝ)))
    (hψ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (seedPathTube β 0 τ (3 * ρ)))
    (hφ : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (seedPathTube β 0 τ (3 * ρ))) :
    Tendsto (seedBandRemainder ψ φ β τ t) atTop (𝓝 0) := by
  have hmesh : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η : ℝ := ε / (t + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hrem⟩ := exists_seed_tube_stepRem_le hρ hβ hψ hφ hη
  filter_upwards [hmesh.eventually_lt_const hδ] with n hn
  let p : ℕ → ℝ≥0 := fun k => min (grid n k) t
  have hp : Monotone p := fun k j hkj => min_le_min_right t (grid_mono n hkj)
  have hb : seedBandRemainder ψ φ β τ t n ≤ η * t := by
    calc _ ≤ ∑ k ∈ Finset.range (cells n), η * ((p (k + 1) : ℝ) - p k) := by
          apply Finset.sum_le_sum
          intro k _
          split_ifs with hh
          · apply hrem
            · exact (p k).coe_nonneg
            · exact_mod_cast hp (Nat.le_succ k)
            · exact_mod_cast hh.2
            · exact (seed_grid_sub_le n k t).trans_lt hn
          · exact mul_nonneg hη.le (sub_nonneg.2 (by exact_mod_cast hp (Nat.le_succ k)))
      _ = η * ((p (cells n) : ℝ) - p 0) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_range_sub (fun k => (p k : ℝ)) (cells n)
      _ ≤ η * t := by
          simp only [p, grid_zero, zero_min, NNReal.coe_zero, sub_zero]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right (grid n (cells n)) t) hη.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (seedBandRemainder_nonneg ψ φ β τ t n)]
  apply hb.trans_lt
  have he : η * (t + 1) = ε := div_mul_cancel₀ _ (by positivity : (t : ℝ) + 1 ≠ 0)
  nlinarith only [he, hη]

end InteractingSLE.ZhanGT4
