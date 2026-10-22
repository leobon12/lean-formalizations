import HigherDimLQGMetric.Coord.RecoveryArc

/-! # Finite-chain assembly for quantitative recovery -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

theorem pathJoinFinite_pair_bound
    {X : Type*} [MetricSpace X] (z : ℕ → X) (N : ℕ)
    (oldStep newStep : ∀ i : ℕ, i < N → Path (z i) (z (i + 1)))
    {r : ℝ} (hr : 0 ≤ r)
    (hstep : ∀ i (hi : i < N) (t : I),
      dist (oldStep i hi t) (newStep i hi t) ≤ r) :
    ∀ i (hi : i ≤ N) (t : I),
      dist (pathJoinFinite z N oldStep i hi t)
        (pathJoinFinite z N newStep i hi t) ≤ r := by
  intro i
  induction i with
  | zero =>
      intro hi t
      simpa [pathJoinFinite] using hr
  | succ i ih =>
      intro hi t
      simp only [pathJoinFinite, Path.trans_apply]
      split_ifs with ht
      · exact ih (by omega) _
      · exact hstep i (by omega) _

theorem recovery_chain_estimate
    {X : Type*} [MetricSpace X]
    (_δ δ' : X → X → ℝ≥0∞) (w : X → ℝ)
    (hself : ∀ x, δ' x x = 0)
    (htri : ∀ p q r, δ' p r ≤ δ' p q + δ' q r)
    (z : ℕ → X) (N : ℕ)
    (oldStep newStep : ∀ i : ℕ, i < N → Path (z i) (z (i + 1)))
    (ℓ : ℕ → ℝ) (oldCost : ℕ → ℝ≥0∞)
    {L Ω M e χ : ℝ} {B : ℝ≥0∞}
    (hℓ : ∀ i < N, 0 ≤ ℓ i)
    (hℓsum : (∑ i ∈ Finset.range N, ℓ i) ≤ L)
    (hΩ : 0 ≤ Ω) (hM : 0 ≤ M) (he : 0 ≤ e) (hχ : 0 ≤ χ)
    (hpieceLen : ∀ i (hi : i < N),
      coordinatePathLength δ' (newStep i hi) ≤ ENNReal.ofReal (ℓ i + e))
    (hpieceWeighted : ∀ i (hi : i < N),
      coordinatePathWeightedLength δ' w (newStep i hi) ≤
        oldCost i + ENNReal.ofReal (2 * Ω * ℓ i + 2 * M * e))
    (hcostsum : (∑ i ∈ Finset.range N, oldCost i) ≤ B)
    (hstepClose : ∀ i (hi : i < N) (t : I),
      dist (oldStep i hi t) (newStep i hi t) ≤ 2 * χ) :
    coordinatePathLength δ' (pathJoinFinite z N newStep N le_rfl) ≤
        ENNReal.ofReal (L + N * e) ∧
      coordinatePathWeightedLength δ' w (pathJoinFinite z N newStep N le_rfl) ≤
        B + ENNReal.ofReal (2 * Ω * L + 2 * M * N * e) ∧
      ∀ t : I, dist (pathJoinFinite z N oldStep N le_rfl t)
        (pathJoinFinite z N newStep N le_rfl t) ≤ 2 * χ := by
  have hL : 0 ≤ L := (Finset.sum_nonneg fun i hi => hℓ i (Finset.mem_range.1 hi)).trans hℓsum
  have hlen : coordinatePathLength δ' (pathJoinFinite z N newStep N le_rfl) ≤
      ENNReal.ofReal (L + N * e) := by
    rw [coordinatePathLength_joinFinite δ' hself htri]
    have hsum : (∑ i ∈ Finset.range N,
        if hi : i < N then coordinatePathLength δ' (newStep i hi) else 0) ≤
        ∑ i ∈ Finset.range N, ENNReal.ofReal (ℓ i + e) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [dite_eq_left (Finset.mem_range.1 hi)] using
        hpieceLen i (Finset.mem_range.1 hi)
    have hnonneg : ∀ i ∈ Finset.range N, 0 ≤ ℓ i + e := by
      intro i hi
      exact add_nonneg (hℓ i (Finset.mem_range.1 hi)) he
    calc
      _ ≤ ∑ i ∈ Finset.range N, ENNReal.ofReal (ℓ i + e) := hsum
      _ = ENNReal.ofReal (∑ i ∈ Finset.range N, (ℓ i + e)) :=
        (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
      _ ≤ ENNReal.ofReal (L + N * e) := by
        apply ENNReal.ofReal_le_ofReal
        have hsum' : (∑ i ∈ Finset.range N, (ℓ i + e)) =
            (∑ i ∈ Finset.range N, ℓ i) + N * e := by
          simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        rw [hsum']
        linarith
  have hweighted : coordinatePathWeightedLength δ' w
      (pathJoinFinite z N newStep N le_rfl) ≤
      B + ENNReal.ofReal (2 * Ω * L + 2 * M * N * e) := by
    rw [coordinatePathWeightedLength_joinFinite δ' hself htri]
    have hsum : (∑ i ∈ Finset.range N,
        if hi : i < N then coordinatePathWeightedLength δ' w (newStep i hi) else 0) ≤
        (∑ i ∈ Finset.range N, oldCost i) +
          (∑ i ∈ Finset.range N, ENNReal.ofReal (2 * Ω * ℓ i + 2 * M * e)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      simpa only [dite_eq_left (Finset.mem_range.1 hi)] using
        hpieceWeighted i (Finset.mem_range.1 hi)
    exact hsum.trans (add_le_add hcostsum
      (weighted_recovery_error_sum_le N ℓ hℓ hℓsum hΩ hM he))
  exact ⟨hlen, hweighted,
    pathJoinFinite_pair_bound z N oldStep newStep (by positivity) hstepClose N le_rfl⟩

end HigherDimLQGMetric
