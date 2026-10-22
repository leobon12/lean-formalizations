import HigherDimLQGContinuity.Network.Topology

/-! # Elementary properties of finite segment samples -/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

theorem segmentSampleCount_pos {d : ℕ} (a b : Rd d) (ω : ℝ) :
    0 < segmentSampleCount a b ω := by
  unfold segmentSampleCount
  omega

theorem segmentSamples_start {d : ℕ} (a b : Rd d) (ω : ℝ) :
    a ∈ segmentSamples a b ω := by
  classical
  unfold segmentSamples
  apply Finset.mem_image.mpr
  refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
  simp

theorem segmentSamples_end {d : ℕ} (a b : Rd d) (ω : ℝ) :
    b ∈ segmentSamples a b ω := by
  classical
  let n := segmentSampleCount a b ω
  have hn : 0 < n := segmentSampleCount_pos a b ω
  unfold segmentSamples
  apply Finset.mem_image.mpr
  refine ⟨n, Finset.mem_range.mpr (by omega), ?_⟩
  simp only [n]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [div_self hnR, one_smul]
  abel

theorem segmentSamples_subset_segment {d : ℕ} (a b : Rd d) (ω : ℝ) :
    ↑(segmentSamples a b ω) ⊆ segment ℝ a b := by
  classical
  intro x hx
  unfold segmentSamples at hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  have hj' : j ≤ segmentSampleCount a b ω := by
    have := Finset.mem_range.mp hj
    omega
  have hn : 0 < segmentSampleCount a b ω := segmentSampleCount_pos a b ω
  rw [segment_eq_image' ℝ a b]
  refine ⟨(j : ℝ) / segmentSampleCount a b ω, ?_, rfl⟩
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact (div_le_one (by exact_mod_cast hn)).mpr (by exact_mod_cast hj')

/-- Consecutive sample centres have overlapping radius-`ω` balls. The stronger
`ω/100` estimate is retained for later tube counts. -/
theorem segmentSamples_step {d : ℕ} (a b : Rd d) {ω : ℝ} (hω : 0 < ω)
    (j : ℕ) :
    dist
      (a + ((j : ℝ) / segmentSampleCount a b ω) • (b - a))
      (a + (((j + 1 : ℕ) : ℝ) / segmentSampleCount a b ω) • (b - a)) ≤
        ω / 100 := by
  let n := segmentSampleCount a b ω
  have hn : 0 < n := segmentSampleCount_pos a b ω
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratio : 100 * dist a b / ω ≤ (n : ℝ) := by
    exact (Nat.le_ceil (100 * dist a b / ω)).trans
      (by exact_mod_cast (Nat.le_max_right 1 ⌈100 * dist a b / ω⌉₊))
  have hcost : dist a b / n ≤ ω / 100 := by
    have hprod : 100 * dist a b ≤ (n : ℝ) * ω :=
      (div_le_iff₀ hω).mp hratio
    apply (div_le_iff₀ hnR).2
    calc
      dist a b ≤ ((n : ℝ) * ω) / 100 :=
        (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).2 (by nlinarith [hprod])
      _ = ω / 100 * n := by ring
  have hline (k : ℕ) :
      a + ((k : ℝ) / n) • (b - a) =
        AffineMap.lineMap a b ((k : ℝ) / n) := by
    simp only [AffineMap.lineMap_apply_module, smul_sub, sub_smul, one_smul]
    abel
  rw [hline j, hline (j + 1), dist_lineMap_lineMap]
  have hparam : dist ((j : ℝ) / n) (((j + 1 : ℕ) : ℝ) / n) = 1 / n := by
    rw [Real.dist_eq]
    have h : (j : ℝ) / n - ((j + 1 : ℕ) : ℝ) / n = -(1 / n) := by
      push_cast
      ring
    rw [h, abs_neg, abs_of_nonneg]
    positivity
  rw [hparam]
  simpa only [one_div, inv_mul_eq_div] using hcost

/-- A finite chain of open balls is connected when each new centre lies in
the preceding ball. -/
theorem connected_ball_chain {d : ℕ} (c : ℕ → Rd d) {ω : ℝ}
    (hω : 0 < ω) (n : ℕ)
    (hstep : ∀ j < n, dist (c j) (c (j + 1)) < ω) :
    IsConnected (⋃ j ∈ Finset.range (n + 1), ball (c j) ω) := by
  induction n with
  | zero =>
      simpa using isConnected_ball hω (x := c 0)
  | succ n ih =>
      have hprev : ∀ j < n, dist (c j) (c (j + 1)) < ω := by
        intro j hj
        exact hstep j (by omega)
      have hconn := ih hprev
      have hmeet :
          ((⋃ j ∈ Finset.range (n + 1), ball (c j) ω) ∩
            ball (c (n + 1)) ω).Nonempty := by
        refine ⟨c n, ?_, ?_⟩
        · exact mem_iUnion₂.mpr
            ⟨n, Finset.mem_range.mpr (by omega), mem_ball_self hω⟩
        · exact mem_ball.mpr (hstep n (by omega))
      have hnew := IsConnected.union hmeet hconn (isConnected_ball hω)
      simpa only [Finset.range_add_one, Finset.set_biUnion_insert,
        union_assoc, union_left_comm, union_comm] using hnew

/-- The open tube balls along one sampled segment form a connected set. -/
theorem connected_segmentSampleBalls {d : ℕ} (a b : Rd d) {ω : ℝ}
    (hω : 0 < ω) :
    IsConnected (⋃ x ∈ segmentSamples a b ω, ball x ω) := by
  let c : ℕ → Rd d := fun j =>
    a + ((j : ℝ) / segmentSampleCount a b ω) • (b - a)
  have hstep : ∀ j < segmentSampleCount a b ω,
      dist (c j) (c (j + 1)) < ω := by
    intro j _
    exact (segmentSamples_step a b hω j).trans_lt (by linarith)
  have hconn := connected_ball_chain c hω (segmentSampleCount a b ω) hstep
  have hEq : (⋃ x ∈ segmentSamples a b ω, ball x ω) =
      ⋃ j ∈ Finset.range (segmentSampleCount a b ω + 1), ball (c j) ω := by
    ext x
    simp only [segmentSamples, c, mem_iUnion, Finset.mem_image]
    aesop
  rw [hEq]
  exact hconn

/-- Finite chain version for arbitrary connected sets. -/
theorem connected_range_chain {α : Type*} [TopologicalSpace α]
    (B : ℕ → Set α) (n : ℕ) (hn : 0 < n)
    (hconn : ∀ j < n, IsConnected (B j))
    (hmeet : ∀ j, j + 1 < n → (B j ∩ B (j + 1)).Nonempty) :
    IsConnected (⋃ j ∈ Finset.range n, B j) := by
  induction n with
  | zero => omega
  | succ m ih =>
      by_cases hm : m = 0
      · subst m
        simpa using hconn 0 (by omega)
      · have hmpos : 0 < m := by omega
        have hprev : ∀ j < m, IsConnected (B j) := by
          intro j hj
          exact hconn j (by omega)
        have hmeetPrev : ∀ j, j + 1 < m → (B j ∩ B (j + 1)).Nonempty := by
          intro j hj
          exact hmeet j (by omega)
        have hbody := ih hmpos hprev hmeetPrev
        have hlast : ((⋃ j ∈ Finset.range m, B j) ∩ B m).Nonempty := by
          obtain ⟨x, hx0, hx1⟩ := hmeet (m - 1) (by omega)
          refine ⟨x, ?_, ?_⟩
          · exact mem_iUnion₂.mpr
              ⟨m - 1, Finset.mem_range.mpr (by omega), hx0⟩
          · simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] using hx1
        have hjoined := IsConnected.union hlast hbody (hconn m (by omega))
        simpa only [Finset.range_add_one, Finset.set_biUnion_insert,
          union_comm] using hjoined

end HigherDimLQGContinuity
