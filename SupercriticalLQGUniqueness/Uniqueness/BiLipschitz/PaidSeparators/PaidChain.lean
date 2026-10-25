import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidStage




 





set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators

 

theorem mem_paid_interval_of_mem_prefix (S : ℕ → ℝ) (hS : Monotone S)
    (hS0 : S 0 = 0) (J : ℕ) {u : ℝ} (hu : u ∈ Ico 0 (S J)) :
    ∃ j < J, u ∈ Ico (S j) (S (j + 1)) := by
  induction J with
  | zero =>
      rw [hS0] at hu
      exact False.elim (not_lt_of_ge hu.1 hu.2)
  | succ J ih =>
      by_cases h : u < S J
      · obtain ⟨j, hj, hju⟩ := ih ⟨hu.1, h⟩
        exact ⟨j, by omega, hju⟩
      · exact ⟨J, Nat.lt_succ_self J,
          ⟨le_of_not_gt h, hu.2⟩⟩

 

theorem exists_selected_component_at_terminal {ι : Type*}
    (F : Finset ι) (V : ι → Set ℂ) {P : ℝ → ℂ} {t T : ℝ}
    (ht : 0 < t) (htT : t ≤ T)
    (hPc : ContinuousOn P (Icc 0 T))
    (hcov : P '' Ico 0 t ⊆ ⋃ i ∈ F, V i) :
    ∃ i ∈ F, P t ∈ closure (V i) := by
  have hcl : closure (Ico (0 : ℝ) t) = Icc 0 t :=
    closure_Ico ht.ne
  have hPc' : ContinuousOn P (closure (Ico 0 t)) := by
    rw [hcl]
    exact hPc.mono (Icc_subset_Icc le_rfl htT)
  have htcl : t ∈ closure (Ico (0 : ℝ) t) := by
    rw [hcl]
    exact right_mem_Icc.2 ht.le
  have hPtcl : P t ∈ closure (P '' Ico 0 t) :=
    hPc'.image_closure ⟨t, htcl, rfl⟩
  have hsubset : P t ∈ closure (⋃ i ∈ F, V i) :=
    closure_mono hcov hPtcl
  rw [Finset.closure_biUnion] at hsubset
  obtain ⟨i, hi, hmem⟩ := mem_iUnion₂.mp hsubset
  exact ⟨i, hi, hmem⟩

 


theorem paid_prefix_trace_chain (D' : LSCMetric)
    {P : ℝ → ℂ} {T : ℝ} (hPc : ContinuousOn P (Icc 0 T))
    (J : ℕ) (hJ : 0 < J) (S : ℕ → ℝ)
    (hS0 : S 0 = 0) (hSmono : Monotone S)
    (hSI : ∀ n, S n ∈ Icc (0 : ℝ) T)
    (K : ℕ → Set ℂ) (c : ℕ → ℂ)
    (Q : ℕ → ℝ → ℂ) (a b : ℕ → ℝ)
    (hcurve : ∀ j < J, D'.IsCurve (Q j) (a j) (b j))
    (htrace : ∀ j < J, K j = Q j '' Icc (a j) (b j))
    (hcompact : ∀ j < J, IsCompact (K j))
    (hconnected : ∀ j < J, IsConnected (K j))
    (hfinite : ∀ j < J, D'.len (Q j) (a j) (b j) < ∞)
    (hbounded : ∀ j < J,
      Bornology.IsBounded (connectedComponentIn (K j)ᶜ (c j)))
    (hpaidStrict : ∀ j < J, S j < S (j + 1))
    (hpaid : ∀ j < J, ∀ u ∈ Ico (S j) (S (j + 1)),
      P u ∈ connectedComponentIn (K j)ᶜ (c j)) :
    ∃ F ⊆ Finset.range J,
      P '' Ico 0 (S J) ⊆
        ⋃ j ∈ F, connectedComponentIn (K j)ᶜ (c j) ∧
      ∀ i ∈ F, ∀ j ∈ F, ∀ x ∈ K i, ∀ y ∈ K j,
        D' (x, y) ≤ ∑ q ∈ F, D'.len (Q q) (a q) (b q) := by
  classical
  have hSJpos : 0 < S J := by
    have h01 : 0 < S 1 := hS0 ▸ hpaidStrict 0 hJ
    exact h01.trans_le (hSmono (by omega : 1 ≤ J))
  let A : Set ℂ := P '' Ico 0 (S J)
  have hAne : A.Nonempty :=
    ⟨P 0, 0, ⟨le_rfl, hSJpos⟩, rfl⟩
  have hApc : IsPreconnected A :=
    isPreconnected_Ico.image P (hPc.mono (Ico_subset_Icc_self.trans
      (Icc_subset_Icc le_rfl (hSI J).2)))
  have hcov : A ⊆ ⋃ j ∈ Finset.range J,
      connectedComponentIn (K j)ᶜ (c j) := by
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨j, hj, huj⟩ := mem_paid_interval_of_mem_prefix S hSmono hS0 J hu
    exact mem_biUnion (Finset.mem_range.mpr hj) (hpaid j hj u huj)
  have hEucl : ∀ j ∈ Finset.range J, ContinuousOn (Q j) (Icc (a j) (b j)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hc : IsCompact (Q j '' Icc (a j) (b j)) := by
      rw [← htrace j hj']
      exact hcompact j hj'
    exact Toolkit.PlanarSeparation.LSCMetric.continuousOn_euclidean_of_bounded D' (Q j)
      (hcurve j hj') hc.isBounded
  obtain ⟨F, hF, hcovF, hchain⟩ :=
    Toolkit.PlanarSeparation.paidTrace_chain D' (Finset.range J) K Q a b c A hAne hApc hcov
      (fun j hj => hcurve j (Finset.mem_range.mp hj)) hEucl
      (fun j hj => htrace j (Finset.mem_range.mp hj))
      (fun j hj => hfinite j (Finset.mem_range.mp hj))
      (fun j hj => hbounded j (Finset.mem_range.mp hj))
  refine ⟨F, hF, hcovF, ?_⟩
  intro i hi j hj x hx y hy
  exact hchain ⟨i, hi⟩ ⟨j, hj⟩ x hx y hy

 

theorem selected_paid_sum_le (D D' : LSCMetric) {P : ℝ → ℂ}
    {T : ℝ} (hT : 0 ≤ T) {A : ℝ} (hA : 1 ≤ A)
    (J : ℕ) (S : ℕ → ℝ) (hS0 : S 0 = 0)
    (hSmono : Monotone S) (hSJ : S J ≤ T)
    (F : Finset ℕ) (hF : F ⊆ Finset.range J)
    (Q : ℕ → ℝ → ℂ) (a b : ℕ → ℝ)
    (hfund : ∀ j < J,
      D'.len (Q j) (a j) (b j) ≤
        ENNReal.ofReal (2 * A ^ 2) * D.len P (S j) (S (j + 1))) :
    (∑ j ∈ F, D'.len (Q j) (a j) (b j)) ≤
      ENNReal.ofReal (2 * A ^ 2) * D.len P 0 T := by
  have hcoef : 0 ≤ 2 * A ^ 2 := by positivity
  calc
    (∑ j ∈ F, D'.len (Q j) (a j) (b j))
        ≤ ∑ j ∈ Finset.range J, D'.len (Q j) (a j) (b j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hF (by simp)
    _ ≤ ∑ j ∈ Finset.range J,
        ENNReal.ofReal (2 * A ^ 2) * D.len P (S j) (S (j + 1)) :=
          Finset.sum_le_sum fun j hj => hfund j (Finset.mem_range.mp hj)
    _ = ENNReal.ofReal (2 * A ^ 2) *
        ∑ j ∈ Finset.range J, D.len P (S j) (S (j + 1)) := by
          rw [Finset.mul_sum]
    _ = ENNReal.ofReal (2 * A ^ 2) * D.len P 0 (S J) := by
          rw [← hS0]
          exact congrArg (fun v : ℝ≥0∞ => ENNReal.ofReal (2 * A ^ 2) * v)
            (LQGMetric.MetricGeometry.sum_curveLength_eq (D.pt ∘ P) hSmono J)
    _ ≤ ENNReal.ofReal (2 * A ^ 2) * D.len P 0 T := by
          gcongr
          exact LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P)
            le_rfl hSJ


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators
