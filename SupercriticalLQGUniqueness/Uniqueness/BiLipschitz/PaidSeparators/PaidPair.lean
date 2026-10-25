import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidChain




 





set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators

theorem finite_stage_pair_bound (D D' : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {A ε : ℝ} (hA : 1 ≤ A) (hε : 0 < ε)
    {P : ℝ → ℂ} {T : ℝ}
    (hP : D.IsCurve P 0 T) (hPc : ContinuousOn P (Icc 0 T))
    (hfin : D.len P 0 T ≠ ∞)
    (hdist : 6 * ε < dist (P 0) (P T))
    {k : ℕ} (x : Fin k → ℂ) (r N : Fin k → ℝ)
    (hr : ∀ i, 0 < r i) (hrε : ∀ i, r i ≤ ε)
    (hgood : ∀ i, GoodScalar D D' A (x i) (r i) (N i) (hr i))
    (hcover : ∀ s ∈ Icc (0 : ℝ) T,
      ∃ i : Fin k, dist (P s) (x i) < r i / 2) :
    ∃ z' w' : ℂ,
      dist z' (P 0) < 7 * ε ∧ dist w' (P T) < 13 * ε ∧
      D' (z', w') ≤ ENNReal.ofReal (2 * A ^ 2) * D.len P 0 T := by
  classical
  obtain ⟨Q, a, b, I, J, S, hdata, hinner, hS0, hSmono, hSI, hpaid, hterminal⟩ :=
    finite_stage_paid_recursion D D' hB hL hA hP hPc hfin x r N hr hgood hcover
  let K : ℕ → Set ℂ := fun j => Q (I (S j)) '' Icc (a (I (S j))) (b (I (S j)))
  let c : ℕ → ℂ := fun j => x (I (S j))
  let V : ℕ → Set ℂ := fun j => connectedComponentIn (K j)ᶜ (c j)
  have hVouter : ∀ j, V j ⊆ ball (c j) (3 * r (I (S j))) :=
    fun j => (hdata (I (S j))).2.2.2.2.2.2
  have hJpos : 0 < J := by
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
    · have hzV : P 0 ∈ V 0 := by
        have h := hterminal 0 (by rw [hJ0, hS0]; exact left_mem_Icc.2 hP.1)
        simpa [V, K, c, hJ0] using h
      have hwV : P T ∈ V 0 := by
        have h := hterminal T (by rw [hJ0, hS0]; exact right_mem_Icc.2 hP.1)
        simpa [V, K, c, hJ0] using h
      have hV0 : V 0 ⊆ ball (c 0) (3 * r (I 0)) := by
        simpa only [hS0] using hVouter 0
      have hclose := component_pair_close (hr (I 0)) (hrε (I 0))
        hV0 hzV hwV
      exact False.elim ((not_lt_of_ge hdist.le) hclose)
    · exact hJ0
  have hSJpos : 0 < S J := by
    have h01 : 0 < S 1 := hS0 ▸ (hpaid 0 hJpos).1
    exact h01.trans_le (hSmono (by omega : 1 ≤ J))
  have hchainData := paid_prefix_trace_chain D' hPc J hJpos S hS0 hSmono hSI
    K c (fun j => Q (I (S j))) (fun j => a (I (S j))) (fun j => b (I (S j)))
    (fun j _ => (hdata (I (S j))).1)
    (fun j _ => rfl)
    (fun j _ => (hdata (I (S j))).2.2.2.1)
    (fun j _ => (hdata (I (S j))).2.2.2.2.1)
    (fun j _ => ((hdata (I (S j))).2.2.1).trans_le le_top)
    (fun j _ => isBounded_ball.subset (hVouter j))
    (fun j hj => (hpaid j hj).1)
    (fun j hj u hu => (hpaid j hj).2.2 u hu)
  obtain ⟨F, hF, hcovF, hchain⟩ := hchainData
  have hzA : P 0 ∈ P '' Ico 0 (S J) :=
    ⟨0, ⟨le_rfl, hSJpos⟩, rfl⟩
  obtain ⟨js, hjsF, hzV⟩ := mem_iUnion₂.mp (hcovF hzA)
  obtain ⟨je, hjeF, hpVcl⟩ :=
    exists_selected_component_at_terminal F V hSJpos (hSI J).2 hPc hcovF
  have hKne : ∀ j, (K j).Nonempty := by
    intro j
    have hq := (hdata (I (S j))).1
    exact ⟨Q (I (S j)) (a (I (S j))),
      a (I (S j)), left_mem_Icc.2 hq.1, rfl⟩
  have hKball : ∀ j, K j ⊆ ball (c j) (3 * r (I (S j))) := by
    intro j y hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact (Toolkit.PlanarSeparation.candidate_annulus_subset_radii
      (sepAnn (x (I (S j))) (r (I (S j))) (hr (I (S j))))
      ((hdata (I (S j))).2.1 u hu)).2
  obtain ⟨z', hz'K, hz'near⟩ :=
    exists_trace_near_component (hr (I (S js))) (hrε (I (S js)))
      (hKne js) (hKball js) (hVouter js) (subset_closure hzV)
  have hpLast : P (S J) ∈ V J := by
    simpa only [V, K, c] using hterminal (S J) (left_mem_Icc.2 (hSI J).2)
  have hwLast : P T ∈ V J := by
    simpa only [V, K, c] using hterminal T (right_mem_Icc.2 (hSI J).2)
  obtain ⟨w', hw'K, hw'near⟩ :=
    exists_trace_near_terminal
      (hr (I (S je))) (hr (I (S J)))
      (hrε (I (S je))) (hrε (I (S J)))
      (hKne je) (hKball je) (hVouter je) hpVcl
      (hVouter J) hpLast hwLast
  have hfund : ∀ j < J,
      D'.len (Q (I (S j))) (a (I (S j))) (b (I (S j))) ≤
        ENNReal.ofReal (2 * A ^ 2) * D.len P (S j) (S (j + 1)) := by
    intro j hj
    have hjpaid := hpaid j hj
    have hsub : Icc (S j) (S (j + 1)) ⊆ Icc (0 : ℝ) T :=
      Icc_subset_Icc (hSI j).1 (hSI (j + 1)).2
    have hcurve : D.IsCurve P (S j) (S (j + 1)) :=
      ⟨hjpaid.1.le, hP.2.mono hsub⟩
    have hstartRad : ‖P (S j) - x (I (S j))‖ ≤ r (I (S j)) := by
      rw [← dist_eq_norm]
      linarith [hinner (S j) (hSI j), hr (I (S j))]
    exact (paid_separator_funded D D' hB hL hA (x (I (S j)))
      (hr (I (S j))) (hgood (I (S j))) hcurve hstartRad
      hjpaid.2.1 ((hdata (I (S j))).2.1)
      ((hdata (I (S j))).2.2.1)).le
  have hsum := selected_paid_sum_le D D' hP.1 hA J S hS0 hSmono
    (hSI J).2 F hF
    (fun j => Q (I (S j))) (fun j => a (I (S j)))
    (fun j => b (I (S j))) hfund
  have hdistBound := hchain js hjsF je hjeF z' hz'K w' hw'K
  refine ⟨z', w', ?_, ?_, hdistBound.trans hsum⟩
  · rwa [dist_comm] at hz'near
  · rwa [dist_comm] at hw'near


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators
