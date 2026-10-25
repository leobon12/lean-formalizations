import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PaidPathCompactness.BoundedPaidPaths




 





set_option autoImplicit false
noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic

variable (D : LSCMetric) (v : ℕ → ℂ)
    (P : ∀ n : ℕ, Path (D.pt (v n)) (D.pt (v (n + 1))))

 
def prefixPath : ∀ n : ℕ, Path (D.pt (v 0)) (D.pt (v (n + 1)))
  | 0 => P 0
  | n + 1 => (prefixPath n).trans (P (n + 1))

theorem prefixPath_length (n : ℕ) :
    pathLength (prefixPath D v P n) =
      ∑ k ∈ Finset.range (n + 1), pathLength (P k) := by
  induction n with
  | zero => simp [prefixPath]
  | succ n ih =>
      change pathLength ((prefixPath D v P n).trans (P (n + 1))) = _
      rw [pathLength_trans, ih]
      exact (Finset.sum_range_succ (fun k => pathLength (P k)) (n + 1)).symm

theorem prefixPath_range {K : Set ℂ}
    (hPK : ∀ n t, (P n t : ℂ) ∈ K) (n : ℕ) (t : unitInterval) :
    (prefixPath D v P n t : ℂ) ∈ K := by
  induction n generalizing t with
  | zero => exact hPK 0 t
  | succ n ih =>
      have htr := Path.trans_range (prefixPath D v P n) (P (n + 1))
      have ht : (prefixPath D v P (n + 1) t) ∈
          Set.range (prefixPath D v P n) ∪ Set.range (P (n + 1)) := by
        change ((prefixPath D v P n).trans (P (n + 1))) t ∈ _
        rw [← htr]
        exact Set.mem_range_self t
      rcases ht with ⟨u, hu⟩ | ⟨u, hu⟩
      · exact hu ▸ ih u
      · exact hu ▸ hPK (n + 1) u

 

theorem infinite_concat_compact {K : Set ℂ} (hK : IsCompact K)
    (hPK : ∀ n t, (P n t : ℂ) ∈ K)
    {x : ℂ} (hv : Tendsto v atTop (nhds x))
    (hfinite : (∑' n, pathLength (P n)) ≠ ∞) :
    ∃ Q : C(unitInterval, ℂ),
      Q 0 = v 0 ∧ Q 1 = x ∧ (∀ t, Q t ∈ K) ∧
      D.IsCurve (fun t => Q (projIcc 0 1 zero_le_one t)) 0 1 ∧
      D.len (fun t => Q (projIcc 0 1 zero_le_one t)) 0 1 ≤
        ∑' n, pathLength (P n) := by
  let R : ℕ → ℝ → ℂ := fun n t =>
    (prefixPath D v P n (projIcc 0 1 zero_le_one t) : ℂ)
  have hcurve : ∀ n, D.IsCurve (R n) 0 1 := by
    intro n
    refine ⟨zero_le_one, ?_⟩
    exact ((prefixPath D v P n).continuous.comp continuous_projIcc).continuousOn
  have htrace : ∀ n t, t ∈ Icc (0 : ℝ) 1 → R n t ∈ K := by
    intro n t _
    exact prefixPath_range D v P hPK n (projIcc 0 1 zero_le_one t)
  have hlen : ∀ n, D.len (R n) 0 1 ≤ ∑' n, pathLength (P n) := by
    intro n
    change pathLength (prefixPath D v P n) ≤ _
    rw [prefixPath_length]
    exact ENNReal.sum_le_tsum _
  have hstart : Tendsto (fun n => R n 0) atTop (nhds (v 0)) := by
    have heq : (fun n => R n 0) = fun _ => v 0 := by
      funext n
      have hs : ((prefixPath D v P n) 0 : ℂ) = v 0 := by
        exact (prefixPath D v P n).source
      simpa [R, LSCMetric.Space, LSCMetric.pt] using hs
    rw [heq]
    exact tendsto_const_nhds
  have hend : Tendsto (fun n => R n 1) atTop (nhds x) := by
    have heq : (fun n => R n 1) = fun n => v (n + 1) := by
      funext n
      have ht : ((prefixPath D v P n) 1 : ℂ) = v (n + 1) := by
        exact (prefixPath D v P n).target
      simpa [R, LSCMetric.Space, LSCMetric.pt] using ht
    rw [heq]
    exact hv.comp (tendsto_add_atTop_nat 1)
  obtain ⟨_, _, Q, _, _, _, hQ0, hQ1, hQK, hQc, hQl⟩ :=
    Toolkit.PaidPathCompactness.boundedPaidPaths_compact D hK R (fun _ => 0) (fun _ => 1)
      hcurve htrace hfinite hlen hstart hend
  exact ⟨Q, hQ0, hQ1, hQK, hQc, hQl⟩

 


theorem infinite_concat_of_shrinking
    (hEucl : ∀ n, @Continuous unitInterval ℂ _ _ (fun t : unitInterval =>
      (id : D.Space → ℂ) (P n t)))
    {x : ℂ} (hv : Tendsto v atTop (nhds x))
    (hshrink : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, ∀ t : unitInterval,
        @dist ℂ _ ((id : D.Space → ℂ) (P n t)) x < ε)
    (hfinite : (∑' n, pathLength (P n)) ≠ ∞) :
    ∃ Q : C(unitInterval, ℂ),
      Q 0 = v 0 ∧ Q 1 = x ∧
      D.IsCurve (fun t => Q (projIcc 0 1 zero_le_one t)) 0 1 ∧
      D.len (fun t => Q (projIcc 0 1 zero_le_one t)) 0 1 ≤
        ∑' n, pathLength (P n) := by
  obtain ⟨N, hN⟩ := hshrink 1 zero_lt_one
  let S : Set ℂ := ⋃ n : ℕ, Set.range (fun t : unitInterval =>
    (id : D.Space → ℂ) (P n t))
  have hfirst : @Bornology.IsBounded ℂ _
      (⋃ n ∈ Finset.range N, Set.range (fun t : unitInterval =>
        (id : D.Space → ℂ) (P n t))) := by
    refine (Bornology.isBounded_biUnion_finset (Finset.range N)).2 ?_
    intro n _
    exact (isCompact_range (hEucl n)).isBounded
  have hS : @Bornology.IsBounded ℂ _ S := by
    refine (hfirst.union (Metric.isBounded_ball (x := x) (r := 1))).subset ?_
    intro z hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    obtain ⟨t, rfl⟩ := hn
    by_cases hnN : n < N
    · exact Or.inl (Set.mem_iUnion_of_mem n
        (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hnN) (Set.mem_range_self t)))
    · exact Or.inr (Metric.mem_ball.mpr (hN n (Nat.le_of_not_lt hnN) t))
  obtain ⟨R, hR⟩ := (@Metric.isBounded_iff_subset_ball ℂ S _ x).mp hS
  have hPK : ∀ n t, (P n t : ℂ) ∈ Metric.closedBall x R := by
    intro n t
    exact (Metric.ball_subset_closedBall (α := ℂ)) (hR (Set.mem_iUnion_of_mem n
      (Set.mem_range_self t)))
  obtain ⟨Q, hQ0, hQ1, _, hQc, hQl⟩ :=
    infinite_concat_compact D v P (isCompact_closedBall x R) hPK hv hfinite
  exact ⟨Q, hQ0, hQ1, hQc, hQl⟩

 

theorem infinite_concat_shrinking_only
    (hEucl : ∀ n, @Continuous unitInterval ℂ _ _ (fun t : unitInterval =>
      (id : D.Space → ℂ) (P n t)))
    {x : ℂ}
    (hshrink : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, ∀ t : unitInterval,
        @dist ℂ _ ((id : D.Space → ℂ) (P n t)) x < ε)
    (hfinite : (∑' n, pathLength (P n)) ≠ ∞) :
    ∃ Q : C(unitInterval, ℂ),
      Q 0 = v 0 ∧ Q 1 = x ∧
      D.IsCurve (fun t => Q (projIcc 0 1 zero_le_one t)) 0 1 ∧
      D.len (fun t => Q (projIcc 0 1 zero_le_one t)) 0 1 ≤
        ∑' n, pathLength (P n) := by
  have hv : Tendsto v atTop (nhds x) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hshrink ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have hs : ((id : D.Space → ℂ) (P n 0)) = v n := by
      simpa [LSCMetric.pt, LSCMetric.Space] using (P n).source
    simpa only [hs] using hN n hn (0 : unitInterval)
  exact infinite_concat_of_shrinking D v P hEucl hv hshrink hfinite

end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic
