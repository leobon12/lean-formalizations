/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishWord

/-!
# One-sided limits of the force boundary data

Packet PROVE-CFCHART2. The finite sums stabilize on each punctured side of a boundary
point. This computes the genuine jumps needed for inverse word classification.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfFinish

open PiecewiseConstantBoundaryData

variable {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
  (vL : Fin nL → ℝ) (vR : Fin nR → ℝ)

open scoped Classical in
/-- The left limit on the nonpositive half-line includes marks at the boundary point. -/
theorem leftLim_force_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    leftLim (forceBoundaryData κ ρL ρR vL vR) y =
      -sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter (fun i => y ≤ vL i), ρL i) := by
  classical
  have hp : ∀ᶠ z in 𝓝[<] y, ∀ i, z < vL i ↔ y ≤ vL i := by
    apply eventually_all.2
    intro i
    by_cases hi : y ≤ vL i
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact iff_of_true (lt_of_lt_of_le hz hi) hi
    · filter_upwards [(lt_mem_nhds (lt_of_not_ge hi)).filter_mono nhdsWithin_le_nhds] with z hz
      exact iff_of_false (not_lt_of_ge hz.le) hi
  have he : forceBoundaryData κ ρL ρR vL vR =ᶠ[𝓝[<] y]
      (fun _ => -sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter (fun i => y ≤ vL i), ρL i)) := by
    filter_upwards [self_mem_nhdsWithin, hp] with z hz hzi
    simp only [forceBoundaryData, lt_of_lt_of_le hz hy, ↓reduceIte, hzi, sleLambda]
  exact (tendsto_const_nhds.congr' he.symm).limUnder_eq

open scoped Classical in
/-- The right limit at a negative point excludes marks at that point. -/
theorem rightLim_force_of_neg {y : ℝ} (hy : y < 0) :
    rightLim (forceBoundaryData κ ρL ρR vL vR) y =
      -sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter (fun i => y < vL i), ρL i) := by
  classical
  have hp : ∀ᶠ z in 𝓝[>] y, ∀ i, z < vL i ↔ y < vL i := by
    apply eventually_all.2
    intro i
    by_cases hi : y < vL i
    · filter_upwards [(gt_mem_nhds hi).filter_mono nhdsWithin_le_nhds] with z hz
      exact iff_of_true hz hi
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact iff_of_false (not_lt_of_ge ((not_lt.1 hi).trans hz.le)) hi
  have he : forceBoundaryData κ ρL ρR vL vR =ᶠ[𝓝[>] y]
      (fun _ => -sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter (fun i => y < vL i), ρL i)) := by
    filter_upwards [(gt_mem_nhds hy).filter_mono nhdsWithin_le_nhds, hp] with z hz hzi
    simp only [forceBoundaryData, hz, ↓reduceIte, hzi, sleLambda]
  exact (tendsto_const_nhds.congr' he.symm).limUnder_eq

open scoped Classical in
/-- The left limit at a positive point excludes marks at that point. -/
theorem leftLim_force_of_pos {y : ℝ} (hy : 0 < y) :
    leftLim (forceBoundaryData κ ρL ρR vL vR) y =
      sleLambda κ * (1 + ∑ j ∈ Finset.univ.filter (fun j => vR j < y), ρR j) := by
  classical
  have hp : ∀ᶠ z in 𝓝[<] y, ∀ j, vR j ≤ z ↔ vR j < y := by
    apply eventually_all.2
    intro j
    by_cases hj : vR j < y
    · filter_upwards [(lt_mem_nhds hj).filter_mono nhdsWithin_le_nhds] with z hz
      exact iff_of_true hz.le hj
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact iff_of_false (not_le_of_gt (lt_of_lt_of_le hz (not_lt.1 hj))) hj
  have he : forceBoundaryData κ ρL ρR vL vR =ᶠ[𝓝[<] y]
      (fun _ => sleLambda κ * (1 + ∑ j ∈ Finset.univ.filter (fun j => vR j < y), ρR j)) := by
    filter_upwards [(lt_mem_nhds hy).filter_mono nhdsWithin_le_nhds, hp] with z hz hzj
    simp only [forceBoundaryData, not_lt_of_ge hz.le, ↓reduceIte, hzj, sleLambda]
  exact (tendsto_const_nhds.congr' he.symm).limUnder_eq

open scoped Classical in
/-- The right limit on the nonnegative half-line includes marks at the boundary point. -/
theorem rightLim_force_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    rightLim (forceBoundaryData κ ρL ρR vL vR) y =
      sleLambda κ * (1 + ∑ j ∈ Finset.univ.filter (fun j => vR j ≤ y), ρR j) := by
  classical
  have hp : ∀ᶠ z in 𝓝[>] y, ∀ j, vR j ≤ z ↔ vR j ≤ y := by
    apply eventually_all.2
    intro j
    by_cases hj : vR j ≤ y
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact iff_of_true (hj.trans hz.le) hj
    · filter_upwards [(gt_mem_nhds (lt_of_not_ge hj)).filter_mono nhdsWithin_le_nhds] with z hz
      exact iff_of_false (not_le_of_gt hz) hj
  have he : forceBoundaryData κ ρL ρR vL vR =ᶠ[𝓝[>] y]
      (fun _ => sleLambda κ * (1 + ∑ j ∈ Finset.univ.filter (fun j => vR j ≤ y), ρR j)) := by
    filter_upwards [self_mem_nhdsWithin, hp] with z hz hzj
    simp only [forceBoundaryData, not_lt_of_ge (hy.trans hz.le), ↓reduceIte, hzj, sleLambda]
  exact (tendsto_const_nhds.congr' he.symm).limUnder_eq

end InteractingSLE.Sec5.CfFinish
