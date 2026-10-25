import Mathlib




 



set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings


 

theorem selected_sum_growth
    (c : ℝ) (hc : 0 ≤ c) (X : ℕ → ℝ)
    (S : Finset ℕ) (j : ℕ) (hj : j ∈ S)
    (hmax : ∀ k ∈ S, k ≤ j)
    (hrec : ∀ i ∈ S,
      c * (∑ k ∈ S.filter (fun k => i < k), X k) ≤ X i) :
    (1 + c) ^ (S.card - 1) * X j ≤ ∑ k ∈ S, X k := by
  classical
  let Q : Finset ℕ → Prop := fun S =>
    ∀ j, j ∈ S →
      (∀ k ∈ S, k ≤ j) →
      (∀ i ∈ S, c * (∑ k ∈ S.filter (fun k => i < k), X k) ≤ X i) →
      (1 + c) ^ (S.card - 1) * X j ≤ ∑ k ∈ S, X k
  have hmain : ∀ S : Finset ℕ, Q S := by
    intro S
    apply Finset.strongInductionOn (p := Q) S
    intro S ih j hj hmax hrec
    let i := S.min' ⟨j, hj⟩
    let T := S.erase i
    have hiS : i ∈ S := Finset.min'_mem S ⟨j, hj⟩
    have hmin : ∀ k ∈ S, i ≤ k := fun k hk => Finset.min'_le S k hk
    have hST : insert i T = S := Finset.insert_erase hiS
    have hfilter_i : S.filter (fun k => i < k) = T := by
      ext k
      simp only [T, Finset.mem_filter, Finset.mem_erase]
      constructor
      · intro hk
        exact ⟨by omega, hk.1⟩
      · intro hk
        have hik : i ≤ k := hmin k hk.2
        exact ⟨hk.2, by omega⟩
    have hreci : c * (∑ k ∈ T, X k) ≤ X i := by
      simpa only [hfilter_i] using hrec i hiS
    rcases T.eq_empty_or_nonempty with hT | hT
    · have hSsingle : S = {i} := by simpa [T, hT] using hST.symm
      have hji : j = i := by
        have hj' : j ∈ ({i} : Finset ℕ) := hSsingle ▸ hj
        simpa using hj'
      rw [hSsingle]
      simp only [Finset.card_singleton, Nat.reduceSub,
        pow_zero, one_mul, Finset.sum_singleton]
      exact le_of_eq (congrArg X hji)
    · have hTsub : T ⊂ S := Finset.erase_ssubset hiS
      have hjT : j ∈ T := by
        by_contra hnot
        have hji : j = i := by
          by_contra hne
          exact hnot (Finset.mem_erase.mpr ⟨hne, hj⟩)
        obtain ⟨k, hkT⟩ := hT
        have hkS : k ∈ S := (Finset.mem_erase.mp hkT).2
        have hik : i ≤ k := hmin k hkS
        have hki : k ≠ i := (Finset.mem_erase.mp hkT).1
        have hkj : k ≤ j := hmax k hkS
        omega
      have hmaxT : ∀ k ∈ T, k ≤ j :=
        fun k hk => hmax k ((Finset.mem_erase.mp hk).2)
      have hrecT : ∀ k ∈ T,
          c * (∑ x ∈ T.filter (fun x => k < x), X x) ≤ X k := by
        intro k hkT
        have hkS : k ∈ S := (Finset.mem_erase.mp hkT).2
        have hik : i < k := by
          have := hmin k hkS
          have hne := (Finset.mem_erase.mp hkT).1
          omega
        have hfilter_k : S.filter (fun x => k < x) =
            T.filter (fun x => k < x) := by
          ext x
          simp only [T, Finset.mem_filter, Finset.mem_erase]
          constructor
          · intro hx
            exact ⟨⟨by omega, hx.1⟩, hx.2⟩
          · intro hx
            exact ⟨hx.1.2, hx.2⟩
        simpa only [hfilter_k] using hrec k hkS
      have hIH := ih T hTsub j hjT hmaxT hrecT
      have hcard : S.card = T.card + 1 :=
        (Finset.card_erase_add_one hiS).symm
      have hTcard : 0 < T.card := Finset.card_pos.mpr hT
      have hpow : S.card - 1 = (T.card - 1) + 1 := by omega
      have hsumS : (∑ k ∈ S, X k) = (∑ k ∈ T, X k) + X i :=
        (Finset.sum_erase_add S X hiS).symm
      calc
        (1 + c) ^ (S.card - 1) * X j =
            (1 + c) * ((1 + c) ^ (T.card - 1) * X j) := by
              rw [hpow, pow_succ]
              ring
        _ ≤ (1 + c) * (∑ k ∈ T, X k) :=
          mul_le_mul_of_nonneg_left hIH (by linarith)
        _ ≤ ∑ k ∈ S, X k := by
          rw [hsumS]
          nlinarith
  exact hmain S j hj hmax hrec

 

theorem selected_first_growth
    (c : ℝ) (hc : 0 < c) (X : ℕ → ℝ)
    (S : Finset ℕ) (hcard : 2 ≤ S.card)
    (j : ℕ) (hj : j ∈ S) (hmax : ∀ k ∈ S, k ≤ j)
    (hrec : ∀ i ∈ S,
      c * (∑ k ∈ S.filter (fun k => i < k), X k) ≤ X i) :
    let i := S.min' ⟨j, hj⟩
    c * (1 + c) ^ (S.card - 2) * X j ≤ X i := by
  classical
  dsimp only
  let i := S.min' ⟨j, hj⟩
  let T := S.erase i
  have hiS : i ∈ S := Finset.min'_mem S ⟨j, hj⟩
  have hmin : ∀ k ∈ S, i ≤ k := fun k hk => Finset.min'_le S k hk
  have hfilter : S.filter (fun k => i < k) = T := by
    ext k
    simp only [T, Finset.mem_filter, Finset.mem_erase]
    constructor
    · intro hk
      exact ⟨by omega, hk.1⟩
    · intro hk
      have hik := hmin k hk.2
      exact ⟨hk.2, by omega⟩
  have hreci : c * (∑ k ∈ T, X k) ≤ X i := by
    simpa only [hfilter] using hrec i hiS
  have hsumS : (∑ k ∈ S, X k) = (∑ k ∈ T, X k) + X i :=
    (Finset.sum_erase_add S X hiS).symm
  have htotal := selected_sum_growth c hc.le X S j hj hmax hrec
  have hpow : S.card - 1 = (S.card - 2) + 1 := by omega
  have htot' : (1 + c) * ((1 + c) ^ (S.card - 2) * X j) ≤
      ∑ k ∈ S, X k := by
    calc
      (1 + c) * ((1 + c) ^ (S.card - 2) * X j) =
          (1 + c) ^ (S.card - 1) * X j := by
            rw [hpow, pow_succ]
            ring
      _ ≤ _ := htotal
  apply (mul_le_mul_iff_of_pos_left (by linarith : 0 < 1 + c)).mp
  calc
    (1 + c) * (c * (1 + c) ^ (S.card - 2) * X j) =
        c * ((1 + c) * ((1 + c) ^ (S.card - 2) * X j)) := by ring
    _ ≤ c * (∑ k ∈ S, X k) :=
      mul_le_mul_of_nonneg_left htot' hc.le
    _ ≤ (1 + c) * X i := by
      rw [hsumS]
      nlinarith [hreci]

 

theorem selected_real_recurrence
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (X : ℕ → ℝ≥0∞) (S : Finset ℕ)
    (hfin : ∀ i ∈ S, X i ≠ ∞)
    (hrec : ∀ i ∈ S,
      (∑ k ∈ S.filter (fun k => i < k), X k) ≤ C * X i) :
    ∀ i ∈ S,
      (1 / C.toReal) *
        (∑ k ∈ S.filter (fun k => i < k), (X k).toReal) ≤
          (X i).toReal := by
  intro i hi
  let T := S.filter (fun k => i < k)
  have hfinT : ∀ k ∈ T, X k ≠ ∞ := by
    intro k hk
    exact hfin k (Finset.mem_filter.mp hk).1
  have hsumfin : (∑ k ∈ T, X k) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr hfinT
  have hprodFin : C * X i ≠ ∞ :=
    ENNReal.mul_ne_top hCtop (hfin i hi)
  have hreal := (ENNReal.toReal_le_toReal hsumfin hprodFin).2 (hrec i hi)
  rw [ENNReal.toReal_sum hfinT, ENNReal.toReal_mul] at hreal
  have hCpos : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  change (1 / C.toReal) * (∑ k ∈ T, (X k).toReal) ≤ (X i).toReal
  rw [one_div, inv_mul_eq_div]
  exact (div_le_iff₀ hCpos).2 (by simpa only [mul_comm] using hreal)

 
theorem selected_first_growth_of_ennreal
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (X : ℕ → ℝ≥0∞) (S : Finset ℕ) (hcard : 2 ≤ S.card)
    (j : ℕ) (hj : j ∈ S) (hmax : ∀ k ∈ S, k ≤ j)
    (hfin : ∀ i ∈ S, X i ≠ ∞)
    (hrec : ∀ i ∈ S,
      (∑ k ∈ S.filter (fun k => i < k), X k) ≤ C * X i) :
    let i := S.min' ⟨j, hj⟩
    (1 / C.toReal) * (1 + 1 / C.toReal) ^ (S.card - 2) *
      (X j).toReal ≤ (X i).toReal := by
  exact selected_first_growth (1 / C.toReal)
    (one_div_pos.mpr (ENNReal.toReal_pos hC0 hCtop))
    (fun i => (X i).toReal) S hcard j hj hmax
    (selected_real_recurrence C hC0 hCtop X S hfin hrec)


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings
