import HigherDimLQGMetric.Coord.RecoveryHelpers

/-!
# Arc length subdivision for quantitative recovery
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry
open scoped ENNReal NNReal

namespace HigherDimLQGMetric

/-- The arithmetic bound on the number of length-`δ` pieces in MA1 A6. -/
theorem exists_subdivision_count {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ L / N ≤ δ ∧ (N : ℝ) ≤ L / δ + 1 := by
  by_cases hL0 : L = 0
  · refine ⟨1, by omega, ?_, ?_⟩
    · simp [hL0, hδ.le]
    · simp [hL0]
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
  let N : ℕ := ⌈L / δ⌉₊
  have hNpos : 0 < N := Nat.ceil_pos.mpr (div_pos hLpos hδ)
  have hNge : L / δ ≤ (N : ℝ) := Nat.le_ceil _
  have hNlt : (N : ℝ) < L / δ + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hL hδ.le)
  refine ⟨N, hNpos, ?_, hNlt.le⟩
  rw [div_le_iff₀ (Nat.cast_pos.2 hNpos)]
  have := mul_le_mul_of_nonneg_right hNge hδ.le
  rw [div_mul_cancel₀ L hδ.ne'] at this
  nlinarith

/-- A finite-length path has an arc-length partition with each piece of length
at most `δ` and at most `L / δ + 1` pieces. -/
theorem exists_arcLength_partition
    {X : Type*} [EMetricSpace X] {x y : X}
    (γ : Path x y) (hfin : pathLength γ ≠ ∞)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∃ hN : 0 < N, (N : ℝ) ≤ (pathLength γ).toReal / δ + 1 ∧
      ∀ i < N,
        curveLength (lengthParam γ.extend 0 1)
          ((IccPartition.uniform (a := 0) (b := (pathLength γ).toReal)
            ENNReal.toReal_nonneg N hN).t i)
          ((IccPartition.uniform (a := 0) (b := (pathLength γ).toReal)
            ENNReal.toReal_nonneg N hN).t (i + 1)) ≤
          ENNReal.ofReal δ := by
  let L : ℝ := (pathLength γ).toReal
  obtain ⟨N, hN, hratio, hcount⟩ := exists_subdivision_count
    (L := L) ENNReal.toReal_nonneg hδ
  refine ⟨N, hN, hcount, ?_⟩
  intro i hi
  let p := IccPartition.uniform (a := 0) (b := L) ENNReal.toReal_nonneg N hN
  have hu := hasUnitSpeedOn_lengthParam zero_le_one
    γ.continuous_extend.continuousOn hfin
  have hi0 : p.t i ∈ Icc (0 : ℝ) L := p.mem_Icc hi.le
  have hi1 : p.t (i + 1) ∈ Icc (0 : ℝ) L := p.mem_Icc (Nat.succ_le_of_lt hi)
  rw [curveLength_of_hasUnitSpeedOn hu hi0 hi1, IccPartition.uniform_step]
  exact ENNReal.ofReal_le_ofReal (by simpa using hratio)

/-- The grid form used when the old curve is already parametrized by length. -/
theorem exists_uniform_recovery_grid {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) :
    ∃ N : ℕ, ∃ hN : 0 < N,
      (N : ℝ) ≤ L / δ + 1 ∧
      (∀ i : ℕ, i < N →
        (IccPartition.uniform (a := 0) (b := L) hL N hN).t (i + 1) -
          (IccPartition.uniform (a := 0) (b := L) hL N hN).t i ≤ δ) ∧
      (Finset.sum (Finset.range N) (fun i =>
        (IccPartition.uniform (a := 0) (b := L) hL N hN).t (i + 1) -
          (IccPartition.uniform (a := 0) (b := L) hL N hN).t i)) = L := by
  obtain ⟨N, hN, hratio, hcount⟩ := exists_subdivision_count hL hδ
  refine ⟨N, hN, hcount, ?_, ?_⟩
  · intro i hi
    rw [IccPartition.uniform_step]
    simpa using hratio
  · let p := IccPartition.uniform (a := 0) (b := L) hL N hN
    have htel (n : ℕ) :
        (∑ i ∈ Finset.range n, (p.t (i + 1) - p.t i)) = p.t n - p.t 0 := by
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; ring
    have h := htel N
    rw [p.zero, show p.t N = L from p.last, sub_zero] at h
    simpa [p, Finset.sum_sub_distrib] using h

end HigherDimLQGMetric
