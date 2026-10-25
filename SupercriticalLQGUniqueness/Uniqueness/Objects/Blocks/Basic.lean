import Mathlib




 















set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Blocks

 

theorem halfPlane_of_small_diam {S : Set ℂ} {r : ℝ} (hr : 0 < r) {s₀ : ℂ} (hs₀ : s₀ ∈ S)
    (hlow : ∀ w ∈ S, 3 / 4 * r ≤ ‖w‖) (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ r / 100) :
    (∀ w ∈ S, 0 < w.re) ∨ (∀ w ∈ S, w.re < 0) ∨ (∀ w ∈ S, 0 < w.im) ∨
      (∀ w ∈ S, w.im < 0) := by
  have h0 : 3 / 4 * r ≤ ‖s₀‖ := hlow s₀ hs₀
  have hsq : ‖s₀‖ ^ 2 = s₀.re ^ 2 + s₀.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hbig : r / 100 < |s₀.re| ∨ r / 100 < |s₀.im| := by
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hre : s₀.re ^ 2 ≤ (r / 100) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have him : s₀.im ^ 2 ≤ (r / 100) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hlo : (3 / 4 * r) ^ 2 ≤ ‖s₀‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h0 2
    nlinarith
  have hre_close : ∀ w ∈ S, |w.re - s₀.re| ≤ r / 100 := fun w hw => by
    have := Complex.abs_re_le_norm (w - s₀)
    rw [Complex.sub_re] at this
    exact this.trans (hdiam w hw s₀ hs₀)
  have him_close : ∀ w ∈ S, |w.im - s₀.im| ≤ r / 100 := fun w hw => by
    have := Complex.abs_im_le_norm (w - s₀)
    rw [Complex.sub_im] at this
    exact this.trans (hdiam w hw s₀ hs₀)
  rcases hbig with hb | hb
  · rcases lt_abs.1 hb with hb' | hb'
    · left
      intro w hw
      have := (abs_le.1 (hre_close w hw)).1
      linarith
    · right; left
      intro w hw
      have := (abs_le.1 (hre_close w hw)).2
      linarith
  · rcases lt_abs.1 hb with hb' | hb'
    · right; right; left
      intro w hw
      have := (abs_le.1 (him_close w hw)).1
      linarith
    · right; right; right
      intro w hw
      have := (abs_le.1 (him_close w hw)).2
      linarith

 


theorem scale_intersection (m : ℕ) (S₁ S₂ : Finset ℕ)
    (h₁ : S₁ ⊆ Finset.Icc m (2 * m)) (h₂ : S₂ ⊆ Finset.Icc m (2 * m))
    (c₁ : (3 / 4 : ℝ) * ((m : ℝ) + 1) ≤ S₁.card) (c₂ : (3 / 4 : ℝ) * ((m : ℝ) + 1) ≤ S₂.card) :
    (S₁ ∩ S₂).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hU : (S₁ ∪ S₂).card ≤ m + 1 := by
    calc (S₁ ∪ S₂).card ≤ (Finset.Icc m (2 * m)).card :=
          Finset.card_le_card (Finset.union_subset h₁ h₂)
      _ = m + 1 := by rw [Nat.card_Icc]; omega
  have hI := Finset.card_union_add_card_inter S₁ S₂
  rw [hempty, Finset.card_empty, add_zero] at hI
  have hle : S₁.card + S₂.card ≤ m + 1 := hI ▸ hU
  have hle' : ((S₁.card : ℝ) + S₂.card) ≤ (m : ℝ) + 1 := by exact_mod_cast hle
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

 

theorem exists_piece_ge {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (I : Finset ι) (hI : I.Nonempty) (A : Set Ω) (B : ι → Set Ω)
    (hcov : A ⊆ ⋃ i ∈ I, B i) : ∃ i ∈ I, μ A ≤ I.card * μ (B i) := by
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image I (fun i => μ (B i)) hI
  refine ⟨i₀, hi₀, ?_⟩
  calc μ A ≤ μ (⋃ i ∈ I, B i) := measure_mono hcov
    _ ≤ ∑ i ∈ I, μ (B i) := measure_biUnion_finset_le I B
    _ ≤ ∑ _i ∈ I, μ (B i₀) := Finset.sum_le_sum hmax
    _ = I.card * μ (B i₀) := by rw [Finset.sum_const, nsmul_eq_mul]

 

theorem half_of_likely {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B : Set Ω)
    {q : ℝ≥0∞} (hq : q ≠ ∞) (hA : q ≤ μ A) (hB : μ Bᶜ ≤ q / 2) : q / 2 ≤ μ (A ∩ B) := by
  have h1 : μ A ≤ μ (A ∩ B) + μ Bᶜ :=
    (measure_le_inter_add_sdiff μ A B).trans (add_le_add_right (measure_mono fun x hx => hx.2) _)
  have h2 : q / 2 + q / 2 ≤ μ (A ∩ B) + q / 2 := by
    rw [ENNReal.add_halves]; exact hA.trans (h1.trans (add_le_add_right hB _))
  exact ENNReal.le_of_add_le_add_right (ENNReal.div_ne_top hq two_ne_zero) h2

 
theorem le_inter_of_null {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A N : Set Ω)
    (hN : μ Nᶜ = 0) : μ A ≤ μ (A ∩ N) := by
  calc μ A ≤ μ (A ∩ N) + μ (A \ N) := measure_le_inter_add_sdiff μ A N
    _ ≤ μ (A ∩ N) + μ Nᶜ := add_le_add_right (measure_mono fun x hx => hx.2) _
    _ = μ (A ∩ N) := by rw [hN, add_zero]

 






theorem t51_bookkeeping {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (H U Reg Sh : Set Ω) (Hn : Fin 4 → Set Ω) (J : Fin 4 → Finset ι) (hJ : ∀ n, (J n).Nonempty)
    (F : Fin 4 → ι → Set Ω) (N : ℕ) (hN : ∀ n, (J n).card ≤ N) {p₀ : ℝ≥0∞} (hp₀ : p₀ ≠ ∞)
    (hH : p₀ ≤ μ H) (hcover : H ⊆ ⋃ n, Hn n)
    (hU : μ Uᶜ ≤ p₀ / 4 / 2) (hReg : μ Regᶜ = 0)
    (hcore : ∀ n, Hn n ∩ U ∩ Reg ⊆ ⋃ j ∈ J n, F n j)
    (hSh : μ Shᶜ ≤ p₀ / 4 / 2 / N / 2) :
    ∃ n : Fin 4, ∃ j ∈ J n, p₀ / 4 / 2 / N / 2 ≤ μ (F n j ∩ Sh) := by
  
  obtain ⟨n, -, hn⟩ := exists_piece_ge μ (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty H Hn
    (by simpa using hcover)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hn
  have hq1 : p₀ / 4 ≤ μ (Hn n) := ENNReal.div_le_of_le_mul' (hH.trans hn)
  have hq1' : p₀ / 4 ≠ ∞ := ENNReal.div_ne_top hp₀ (by norm_num)
  
  have hq2 : p₀ / 4 / 2 ≤ μ (Hn n ∩ U) := half_of_likely μ _ _ hq1' hq1 hU
  have hq3 : p₀ / 4 / 2 ≤ μ (Hn n ∩ U ∩ Reg) := hq2.trans (le_inter_of_null μ _ _ hReg)
  
  obtain ⟨j, hj, hjle⟩ := exists_piece_ge μ (J n) (hJ n) _ (F n) (hcore n)
  have hNpos : 0 < N := lt_of_lt_of_le (Finset.card_pos.2 (hJ n)) (hN n)
  have hcard : (N : ℝ≥0∞) ≠ 0 := by simpa using hNpos.ne'
  have hle : μ (Hn n ∩ U ∩ Reg) ≤ μ (F n j) * N := by
    rw [mul_comm]
    exact hjle.trans (mul_le_mul_left (by exact_mod_cast hN n) _)
  have hq4 : p₀ / 4 / 2 / N ≤ μ (F n j) := ENNReal.div_le_of_le_mul (hq3.trans hle)
  have hq4' : p₀ / 4 / 2 / N ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.div_ne_top hq1' two_ne_zero) hcard
  
  exact ⟨n, j, hj, half_of_likely μ _ _ hq4' hq4 hSh⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.Blocks

