import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPUniformBall

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.MetricGeometry

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem lfppDOn_le_of_unitSpeed_mesh
    (ξ : ℝ) (φ : C(ℂ, ℝ))
    {K U : Set ℂ} {Q : ℝ → ℂ} {L : ℝ}
    (hL : 0 ≤ L)
    (hunit : HasUnitSpeedOn
      ((PfeWeyl.lfppLSCMetric ξ φ).pt ∘ Q) (Icc 0 L))
    (hQK : ∀ t ∈ Icc 0 L, Q t ∈ K)
    {r m δ : ℝ} (hr : 0 < r) (hm : 0 ≤ m) (hδ : 0 < δ)
    (hball : ∀ x ∈ K, Metric.closedBall x r ⊆ U ∧
      ∀ u ∈ Metric.closedBall x r, m ≤ Real.exp (ξ * φ u))
    (N : ℕ)
    (hbudget : L / (N + 1 : ℝ) + δ ≤ m * r) :
    lfppDOn ξ φ U (Q 0) (Q L) ≤
      ∑ _i ∈ Finset.range (N + 1),
        (ENNReal.ofReal (L / (N + 1 : ℝ)) + ENNReal.ofReal δ) := by
  let E := PfeWeyl.lfppLSCMetric ξ φ
  let v : ℕ → ℂ := fun i =>
    Q (uniformTime N L
      ⟨min i (N + 1), by omega⟩)
  have hvU : ∀ i, v i ∈ U := by
    intro i
    exact (hball _ (hQK _ (uniformTime_mem N hL _))).1
      (Metric.mem_closedBall_self hr.le)
  have hv0 : v 0 = Q 0 := by
    simp [v, uniformTime_first]
  have hvlast : v (N + 1) = Q L := by
    have hlast : uniformTime N L (⟨N + 1, by omega⟩ : Fin (N + 2)) = L := by
      simpa only [Fin.last] using uniformTime_last N L
    simpa [v, hlast]
  have hstep : ∀ i ∈ Finset.range (N + 1),
      lfppDOn ξ φ U (v i) (v (i + 1)) ≤
        ENNReal.ofReal (L / (N + 1 : ℝ)) + ENNReal.ofReal δ := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    let j : Fin (N + 1) := ⟨i, by omega⟩
    have hvj : v i = Q (uniformTime N L (Fin.castSucc j)) := by
      simp [v, j, min_eq_left (by omega : i ≤ N + 1)]
    have hvj1 : v (i + 1) = Q (uniformTime N L j.succ) := by
      simp [v, j, min_eq_left (by omega : i + 1 ≤ N + 1)]
    have hj0 := uniformTime_mem N hL (Fin.castSucc j)
    have hj1 := uniformTime_mem N hL j.succ
    have hdist : lfppD ξ φ (v i) (v (i + 1)) ≤
        ENNReal.ofReal (L / (N + 1 : ℝ)) := by
      rw [hvj, hvj1]
      have he := edist_le_curveLength (E.pt ∘ Q) (uniformTime_mono N hL j)
      change edist (E.pt (Q (uniformTime N L (Fin.castSucc j))))
        (E.pt (Q (uniformTime N L j.succ))) ≤
        E.len Q (uniformTime N L (Fin.castSucc j))
          (uniformTime N L j.succ) at he
      rw [LSCMetric.edist_pt] at he
      rw [uniformTime_subarc_len E hL hunit N j] at he
      simpa [E, PfeWeyl.lfppLSCMetric_apply,
        B2.LscTop.lfppDistance_eq_lfppD] using he
    have hsmall : lfppD ξ φ (v i) (v (i + 1)) + ENNReal.ofReal δ ≤
        ENNReal.ofReal (m * r) := by
      calc
        _ ≤ ENNReal.ofReal (L / (N + 1 : ℝ)) + ENNReal.ofReal δ :=
          add_le_add hdist le_rfl
        _ = ENNReal.ofReal (L / (N + 1 : ℝ) + δ) := by
          rw [ENNReal.ofReal_add (div_nonneg hL (by positivity)) hδ.le]
        _ ≤ ENNReal.ofReal (m * r) := ENNReal.ofReal_le_ofReal hbudget
    rw [hvj] at hsmall hdist ⊢
    have hloc := lfppDOn_lt_global_add_of_ball φ.continuous hr hm
      (hball _ (hQK _ hj0)).2 (hball _ (hQK _ hj0)).1
      hδ hsmall
    exact hloc.le.trans (add_le_add hdist le_rfl)
  calc
    lfppDOn ξ φ U (Q 0) (Q L) =
        lfppDOn ξ φ U (v 0) (v (N + 1)) := by rw [hv0, hvlast]
    _ ≤ ∑ i ∈ Finset.range (N + 1),
          lfppDOn ξ φ U (v i) (v (i + 1)) :=
      lfppDOn_le_sum_of_vertices v hvU (N + 1)
    _ ≤ ∑ _i ∈ Finset.range (N + 1),
          (ENNReal.ofReal (L / (N + 1 : ℝ)) + ENNReal.ofReal δ) :=
      Finset.sum_le_sum hstep

end SupercriticalLQGUniqueness.B2.PfeAxioms
