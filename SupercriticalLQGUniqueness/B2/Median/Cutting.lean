import SupercriticalLQGUniqueness.B2.Median.Surgery

 










set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.Median

 
def OneSidedOn (P : ℝ → ℂ) (I : Set ℝ) : Prop :=
  (∀ t ∈ I, (P t).im < 2 / 3) ∨ (∀ t ∈ I, 1 / 3 < (P t).im)

 
theorem oneSidedOn_of_short {P : ℝ → ℂ} {a b δ : ℝ} {I : Set ℝ}
    (hδ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      (P s).im ≤ 1 / 3 → 2 / 3 ≤ (P t).im → δ ≤ dist s t)
    (hI : I ⊆ Icc a b) (hshort : ∀ s ∈ I, ∀ t ∈ I, dist s t < δ) :
    OneSidedOn P I := by
  by_cases h : ∃ t ∈ I, 2 / 3 ≤ (P t).im
  · obtain ⟨t, ht, hti⟩ := h
    right
    intro s hs
    by_contra hns
    exact (not_le.mpr (hshort s hs t ht)) (hδ s (hI hs) t (hI ht) (not_lt.mp hns) hti)
  · left
    intro t ht
    by_contra hnt
    exact h ⟨t, ht, not_lt.mp hnt⟩

 

theorem exists_one_sided_cuts {P : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hP : ContinuousOn P (Icc a b))
    (hsq : ∀ t ∈ Icc a b, 0 ≤ (P t).im ∧ (P t).im ≤ 1) :
    ∃ (m : ℕ) (τ : ℕ → ℝ), 0 < m ∧ τ 0 = a ∧ τ m = b ∧
      (∀ j < m, τ j < τ (j + 1)) ∧
      (∀ j, 0 < j → j < m → 0 < (P (τ j)).im ∧ (P (τ j)).im < 1) ∧
      (∀ j < m, OneSidedOn P (Icc (τ j) (τ (j + 1)))) := by
  obtain ⟨δ, hδ0, hδ⟩ := height_alternation_has_min_time hP
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (sub_nonneg.mpr hab.le) hδ0.le) hN
  have hN1 : 1 ≤ N := by exact_mod_cast hNpos
  set hm : ℝ := (b - a) / N with hhm
  have hhm0 : 0 < hm := div_pos (sub_pos.mpr hab) hNpos
  have hhmδ : hm < δ := by
    rw [hhm, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ0] at hN
    linarith
  let t : ℕ → ℝ := fun k => a + k * hm
  have ht0 : t 0 = a := by simp [t]
  have htN : t N = b := by
    simp only [t, hhm]
    field_simp
    ring
  have htsucc : ∀ k, t (k + 1) = t k + hm := by
    intro k
    simp only [t]
    push_cast
    ring
  have htlt : ∀ k, t k < t (k + 1) := fun k => by rw [htsucc]; linarith
  have htmem : ∀ k ≤ N, t k ∈ Icc a b := by
    intro k hk
    refine ⟨?_, ?_⟩
    · simp only [t]
      nlinarith [hhm0.le, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    · have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
      rw [← htN]
      simp only [t]
      nlinarith
  have hstep : ∀ k < N, Icc (t k) (t (k + 1)) ⊆ Icc a b := by
    intro k hk
    exact Icc_subset_Icc (htmem k hk.le).1 (htmem (k + 1) hk).2
  have hshort : ∀ k, ∀ s ∈ Icc (t k) (t (k + 1)), ∀ u ∈ Icc (t k) (t (k + 1)),
      dist s u < δ := by
    intro k s hs u hu
    rw [Real.dist_eq, htsucc] at *
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2, hu.1, hu.2]
  
  have key : ∀ k, 1 ≤ k → k ≤ N →
      ∃ (m : ℕ) (τ : ℕ → ℝ), 0 < m ∧ τ 0 = a ∧ τ m = t k ∧
        (∀ j < m, τ j < τ (j + 1)) ∧
        (∀ j, 0 < j → j < m → 0 < (P (τ j)).im ∧ (P (τ j)).im < 1) ∧
        (∀ j < m, OneSidedOn P (Icc (τ j) (τ (j + 1)))) := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro hN1'
      refine ⟨1, fun j => if j = 0 then a else t 1, one_pos, by simp, by simp, ?_, ?_, ?_⟩
      · intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        simpa [ht0] using htlt 0
      · intro j hj0 hj1
        omega
      · intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        have := oneSidedOn_of_short hδ (hstep 0 (by omega)) (hshort 0)
        simpa [ht0] using this
    | succ k hk1 ih =>
      intro hkN
      obtain ⟨m, τ, hm0, hτ0, hτm, hτmono, hτstrip, hτside⟩ := ih (by omega)
      have hkN' : k < N := by omega
      by_cases hopen : 0 < (P (t k)).im ∧ (P (t k)).im < 1
      · 
        refine ⟨m + 1, fun j => if j = m + 1 then t (k + 1) else τ j, by omega,
          by simp [hτ0], by simp, ?_, ?_, ?_⟩
        · intro j hj
          by_cases hjm : j = m
          · subst hjm
            simp only [if_neg (Nat.succ_ne_self j).symm, if_pos rfl]
            exact hτm ▸ htlt k
          · have hjm' : j < m := by omega
            simp only [if_neg (show j ≠ m + 1 by omega), if_neg (show j + 1 ≠ m + 1 by omega)]
            exact hτmono j hjm'
        · intro j hj0 hjm
          simp only [if_neg (show j ≠ m + 1 by omega)]
          by_cases hjm' : j = m
          · subst hjm'
            exact hτm ▸ hopen
          · exact hτstrip j hj0 (by omega)
        · intro j hj
          by_cases hjm : j = m
          · subst hjm
            simp only [if_neg (Nat.succ_ne_self j).symm, if_pos rfl]
            rw [hτm]
            exact oneSidedOn_of_short hδ (hstep k hkN') (hshort k)
          · simp only [if_neg (show j ≠ m + 1 by omega), if_neg (show j + 1 ≠ m + 1 by omega)]
            exact hτside j (by omega)
      · 
        have hside : (P (t k)).im = 0 ∨ (P (t k)).im = 1 := by
          have hsqk := hsq (t k) (htmem k hkN'.le)
          by_cases h0 : (P (t k)).im = 0
          · exact Or.inl h0
          · right
            by_contra h1
            exact hopen ⟨lt_of_le_of_ne hsqk.1 (Ne.symm h0), lt_of_le_of_ne hsqk.2 h1⟩
        obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
        refine ⟨m₀ + 1, fun j => if j = m₀ + 1 then t (k + 1) else τ j, by omega,
          by simp [hτ0], by simp, ?_, ?_, ?_⟩
        · intro j hj
          by_cases hjm : j = m₀
          · subst hjm
            simp only [if_neg (Nat.succ_ne_self j).symm, if_pos rfl]
            exact (hτmono j (by omega)).trans (hτm ▸ htlt k)
          · simp only [if_neg (show j ≠ m₀ + 1 by omega),
              if_neg (show j + 1 ≠ m₀ + 1 by omega)]
            exact hτmono j (by omega)
        · intro j hj0 hjm
          simp only [if_neg (show j ≠ m₀ + 1 by omega)]
          exact hτstrip j hj0 hjm
        · intro j hj
          by_cases hjm : j = m₀
          · subst hjm
            simp only [if_neg (Nat.succ_ne_self j).symm, if_pos rfl]
            have hold := hτside j (by omega)
            have hτjk : τ j ≤ t k := hτm ▸ (hτmono j (by omega)).le
            have hmemk : t k ∈ Icc (τ j) (τ (j + 1)) := ⟨hτjk, hτm.ge⟩
            have hτjmem : τ j ∈ Icc a b := by
              rcases Nat.eq_zero_or_pos j with hj0 | hj0
              · subst hj0; rw [hτ0]; exact left_mem_Icc.mpr hab.le
              · exact ⟨hτ0 ▸ (show τ 0 ≤ τ j from by
                    have hmono : ∀ i ≤ j, τ 0 ≤ τ i := by
                      intro i hi
                      induction i with
                      | zero => exact le_rfl
                      | succ i ih => exact (ih (by omega)).trans (hτmono i (by omega)).le
                    exact hmono j le_rfl), hτjk.trans (htmem k hkN'.le).2⟩
            have hsub : Icc (τ j) (t (k + 1)) ⊆ Icc a b :=
              Icc_subset_Icc hτjmem.1 (htmem (k + 1) hkN).2
            rcases hside with h0 | h1
            · 
              left
              have hlow : ∀ s ∈ Icc (τ j) (τ (j + 1)), (P s).im < 2 / 3 := by
                rcases hold with hl | hh
                · exact hl
                · have := hh (t k) hmemk
                  rw [h0] at this
                  norm_num at this
              intro s hs
              by_cases hsk : s ≤ t k
              · exact hlow s ⟨hs.1, hτm ▸ hsk⟩
              · have hs' : s ∈ Icc (t k) (t (k + 1)) := ⟨(not_le.mp hsk).le, hs.2⟩
                by_contra hns
                have hd := hδ (t k) (htmem k hkN'.le) s (hsub hs) (by rw [h0]; norm_num)
                  (not_lt.mp hns)
                exact (not_le.mpr (hshort k (t k) (left_mem_Icc.mpr (htlt k).le) s hs')) hd
            · 
              right
              have hhigh : ∀ s ∈ Icc (τ j) (τ (j + 1)), 1 / 3 < (P s).im := by
                rcases hold with hl | hh
                · have := hl (t k) hmemk
                  rw [h1] at this
                  norm_num at this
                · exact hh
              intro s hs
              by_cases hsk : s ≤ t k
              · exact hhigh s ⟨hs.1, hτm ▸ hsk⟩
              · have hs' : s ∈ Icc (t k) (t (k + 1)) := ⟨(not_le.mp hsk).le, hs.2⟩
                by_contra hns
                have hd := hδ s (hsub hs) (t k) (htmem k hkN'.le) (not_lt.mp hns)
                  (by rw [h1]; norm_num)
                rw [dist_comm] at hd
                exact (not_le.mpr (hshort k (t k) (left_mem_Icc.mpr (htlt k).le) s hs')) hd
          · simp only [if_neg (show j ≠ m₀ + 1 by omega),
              if_neg (show j + 1 ≠ m₀ + 1 by omega)]
            exact hτside j (by omega)
  obtain ⟨m, τ, hm0, hτ0, hτm, hτmono, hτstrip, hτside⟩ := key N hN1 le_rfl
  exact ⟨m, τ, hm0, hτ0, hτm.trans htN, hτmono, hτstrip, hτside⟩

end SupercriticalLQGUniqueness.B2.Median
