import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidRecursion




 





set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators

 

theorem finite_stage_paid_recursion (D D' : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {A : ℝ} (hA : 1 ≤ A) {P : ℝ → ℂ} {T : ℝ}
    (hP : D.IsCurve P 0 T) (hPc : ContinuousOn P (Icc 0 T))
    (hfin : D.len P 0 T ≠ ∞)
    {k : ℕ} (x : Fin k → ℂ) (r N : Fin k → ℝ)
    (hr : ∀ i, 0 < r i)
    (hgood : ∀ i, GoodScalar D D' A (x i) (r i) (N i) (hr i))
    (hcover : ∀ s ∈ Icc (0 : ℝ) T,
      ∃ i : Fin k, dist (P s) (x i) < r i / 2) :
    ∃ (Q : Fin k → ℝ → ℂ) (a b : Fin k → ℝ)
      (I : ℝ → Fin k) (J : ℕ) (S : ℕ → ℝ),
      (∀ i,
        D'.IsCurve (Q i) (a i) (b i) ∧
        (∀ t ∈ Icc (a i) (b i), Q i t ∈ (sepAnn (x i) (r i) (hr i)).toSet) ∧
        D'.len (Q i) (a i) (b i) < ENNReal.ofReal (2 * A * N i) ∧
        IsCompact (Q i '' Icc (a i) (b i)) ∧
        IsConnected (Q i '' Icc (a i) (b i)) ∧
        closedBall (x i) (2 * r i) ⊆
          connectedComponentIn (Q i '' Icc (a i) (b i))ᶜ (x i) ∧
        connectedComponentIn (Q i '' Icc (a i) (b i))ᶜ (x i) ⊆
          ball (x i) (3 * r i)) ∧
      (∀ s ∈ Icc (0 : ℝ) T, dist (P s) (x (I s)) < r (I s) / 2) ∧
      S 0 = 0 ∧ Monotone S ∧ (∀ n, S n ∈ Icc (0 : ℝ) T) ∧
      (∀ j < J, S j < S (j + 1) ∧
        P (S (j + 1)) ∈ Q (I (S j)) '' Icc (a (I (S j))) (b (I (S j))) ∧
        ∀ u ∈ Ico (S j) (S (j + 1)),
          P u ∈ connectedComponentIn
            (Q (I (S j)) '' Icc (a (I (S j))) (b (I (S j))))ᶜ
            (x (I (S j)))) ∧
      (∀ u ∈ Icc (S J) T,
        P u ∈ connectedComponentIn
          (Q (I (S J)) '' Icc (a (I (S J))) (b (I (S J))))ᶜ
          (x (I (S J)))) := by
  classical
  obtain ⟨Q, a, b, hdata⟩ := finite_stage_separator_data D D' hA x r N hr hgood
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hP.1⟩
  obtain ⟨i₀, -⟩ := hcover 0 hI0
  letI : Nonempty (Fin k) := ⟨i₀⟩
  choose! I hinner using hcover
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  obtain ⟨η, hη, hηle⟩ :=
    finite_stage_min_cost (I 0) N hApos (fun i => (hgood i).1)
  let K : Fin k → Set ℂ := fun i => Q i '' Icc (a i) (b i)
  have hK : ∀ i, IsClosed (K i) := fun i => (hdata i).2.2.2.1.isClosed
  have hstart : ∀ s ∈ Icc (0 : ℝ) T,
      P s ∈ connectedComponentIn (K (I s))ᶜ (x (I s)) := by
    intro s hs
    have hrad : dist (P s) (x (I s)) ≤ 2 * r (I s) := by
      linarith [hinner s hs, hr (I s)]
    exact (hdata (I s)).2.2.2.2.2.1 (by simpa only [mem_closedBall] using hrad)
  have hcost : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc s T,
      P t ∈ K (I s) → ENNReal.ofReal η ≤ D.len P s t := by
    intro s hs t ht htK
    have hsub : Icc s t ⊆ Icc (0 : ℝ) T :=
      Icc_subset_Icc hs.1 ht.2
    have hcurve : D.IsCurve P s t := ⟨ht.1, hP.2.mono hsub⟩
    have hstartRad : ‖P s - x (I s)‖ ≤ r (I s) := by
      rw [← dist_eq_norm]
      linarith [hinner s hs, hr (I s)]
    obtain ⟨u, hu, hPu⟩ := htK
    have hrad := Toolkit.PlanarSeparation.candidate_annulus_subset_radii
      (sepAnn (x (I s)) (r (I s)) (hr (I s)))
      ((hdata (I s)).2.1 u hu)
    have hendRad : 2 * r (I s) ≤ ‖P t - x (I s)‖ := by
      rw [← hPu]
      have hrad' : 2 * r (I s) < ‖Q (I s) u - x (I s)‖ := by
        simpa only [sepAnn, EuclideanAnnulus.innerRadius,
          EuclideanAnnulus.center, dist_eq_norm] using hrad.1
      exact hrad'.le
    calc
      ENNReal.ofReal η ≤ ENNReal.ofReal (N (I s) / A) :=
        ENNReal.ofReal_le_ofReal (hηle (I s))
      _ ≤ acrossDist D (eblAcrossAnn (x (I s)) (r (I s)) (hr (I s))) :=
        (hgood (I s)).2.1
      _ ≤ D.len P s t := paid_crossing_le_length D hB hL
        (x (I s)) (hr (I s)) hcurve hstartRad hendRad
  obtain ⟨J, S, hS0, hSmono, hSI, hpaid, hterminal⟩ :=
    finite_first_hit_recursion D hP hPc hfin hη K x I hK hstart hcost
  exact ⟨Q, a, b, I, J, S, hdata, hinner, hS0, hSmono, hSI, hpaid, hterminal⟩


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators
