import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 





set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability

private def latticePoint (a : ℝ) (mn : ℤ × ℤ) : ℂ :=
  ((a * mn.1 : ℝ) : ℂ) + ((a * mn.2 : ℝ) : ℂ) * Complex.I

private theorem latticePoint_injective {a : ℝ} (ha : a ≠ 0) :
    Function.Injective (latticePoint a) := by
  intro mn pq h
  have hre : a * (mn.1 : ℝ) = a * (pq.1 : ℝ) := by
    have := congrArg Complex.re h
    simpa [latticePoint] using this
  have him : a * (mn.2 : ℝ) = a * (pq.2 : ℝ) := by
    have := congrArg Complex.im h
    simpa [latticePoint] using this
  have h1 : mn.1 = pq.1 := by
    exact_mod_cast (mul_left_cancel₀ ha hre)
  have h2 : mn.2 = pq.2 := by
    exact_mod_cast (mul_left_cancel₀ ha him)
  exact Prod.ext h1 h2

private theorem grid_ball_subset_box (a R : ℝ) (N : ℕ)
    (ha : 0 < a) (hR : R ≤ a * (N : ℝ)) :
    Objects.CorrectedEvent.grid a ∩ ball 0 R ⊆
      latticePoint a '' ((Set.Icc (-(N : ℤ)) N) ×ˢ (Set.Icc (-(N : ℤ)) N)) := by
  intro z hz
  obtain ⟨m, n, rfl⟩ := hz.1
  have hnorm : ‖latticePoint a (m, n)‖ < R := by
    simpa [latticePoint, dist_eq_norm] using hz.2
  have hmabs : |a * (m : ℝ)| < a * (N : ℝ) := by
    have h : |a * (m : ℝ)| ≤ ‖latticePoint a (m, n)‖ := by
      simpa [latticePoint] using Complex.abs_re_le_norm (latticePoint a (m, n))
    exact lt_of_le_of_lt h (lt_of_lt_of_le hnorm hR)
  have hnabs : |a * (n : ℝ)| < a * (N : ℝ) := by
    have h : |a * (n : ℝ)| ≤ ‖latticePoint a (m, n)‖ := by
      simpa [latticePoint] using Complex.abs_im_le_norm (latticePoint a (m, n))
    exact lt_of_le_of_lt h (lt_of_lt_of_le hnorm hR)
  have hmlo : -(N : ℤ) ≤ m := by
    have h : -(N : ℝ) < (m : ℝ) := lt_of_mul_lt_mul_left (by
      have := (abs_lt.mp hmabs).1
      nlinarith) ha.le
    exact_mod_cast le_of_lt h
  have hmhi : m ≤ (N : ℤ) := by
    have h : (m : ℝ) < (N : ℝ) := lt_of_mul_lt_mul_left
      (lt_of_le_of_lt (le_abs_self _) hmabs) ha.le
    exact_mod_cast le_of_lt h
  have hnlo : -(N : ℤ) ≤ n := by
    have h : -(N : ℝ) < (n : ℝ) := lt_of_mul_lt_mul_left (by
      have := (abs_lt.mp hnabs).1
      nlinarith) ha.le
    exact_mod_cast le_of_lt h
  have hnhi : n ≤ (N : ℤ) := by
    have h : (n : ℝ) < (N : ℝ) := lt_of_mul_lt_mul_left
      (lt_of_le_of_lt (le_abs_self _) hnabs) ha.le
    exact_mod_cast le_of_lt h
  refine ⟨(m, n), ?_, rfl⟩
  exact ⟨⟨hmlo, hmhi⟩, ⟨hnlo, hnhi⟩⟩

private theorem grid_ball_ncard_le (a R : ℝ) (N : ℕ)
    (ha : 0 < a) (hR : R ≤ a * (N : ℝ)) :
    (Objects.CorrectedEvent.grid a ∩ ball 0 R).ncard ≤ (2 * N + 1) ^ 2 := by
  let B : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(N : ℤ)) N).product (Finset.Icc (-(N : ℤ)) N)
  have hsub : Objects.CorrectedEvent.grid a ∩ ball 0 R ⊆ latticePoint a '' (B : Set (ℤ × ℤ)) := by
    simpa [B, Finset.coe_product] using grid_ball_subset_box a R N ha hR
  have hcard : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
    have h := Int.card_Icc_of_le (a := -(N : ℤ)) (b := (N : ℤ)) (by omega)
    omega
  calc
    (Objects.CorrectedEvent.grid a ∩ ball 0 R).ncard ≤ (latticePoint a '' (B : Set (ℤ × ℤ))).ncard :=
      Set.ncard_le_ncard hsub (B.finite_toSet.image _)
    _ ≤ B.card := by simpa using Set.ncard_image_le (f := latticePoint a) (s := (B : Set (ℤ × ℤ)))
    _ = (2 * N + 1) ^ 2 := by simp [B, Finset.card_product, hcard, pow_two]

private theorem lam_mul_pow (k : ℕ) :
    Objects.CorrectedEvent.lam k * (2 : ℝ) ^ k = 1 := by
  rw [Objects.CorrectedEvent.lam, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [Real.rpow_natCast]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))

private theorem regSites_subset_grid_ball (C : Objects.CorrectedEvent.Constants) (k : ℕ) :
    Objects.CorrectedEvent.regSites C k ⊆
      Objects.CorrectedEvent.grid (Objects.CorrectedEvent.lam k * C.r / 4) ∩ ball 0 (4 * C.r) := by
  intro z hz
  have hlam : 0 < Objects.CorrectedEvent.lam k := by
    unfold Objects.CorrectedEvent.lam
    positivity
  have hrad : 0 < 2 * (4 : ℝ) ^ (Objects.CorrectedEvent.regK k) * Objects.CorrectedEvent.lam k * C.r := by
    exact mul_pos (mul_pos (mul_pos (by norm_num)
      (pow_pos (by norm_num) _)) hlam) C.rPos
  have hzn := hz.2 (mem_ball_self hrad)
  exact ⟨hz.1, by
    have hzn' : dist z 0 < 4 * C.r := hzn.2
    simpa [Metric.mem_ball] using hzn'⟩

 

theorem regSites_ncard_le (C : Objects.CorrectedEvent.Constants) (k : ℕ) :
    (Objects.CorrectedEvent.regSites C k).ncard ≤ 1089 * 4 ^ k := by
  let a := Objects.CorrectedEvent.lam k * C.r / 4
  let N := 16 * 2 ^ k
  have hlam : 0 < Objects.CorrectedEvent.lam k := by
    unfold Objects.CorrectedEvent.lam
    positivity
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos hlam C.rPos) (by norm_num)
  have hscale : 4 * C.r ≤ a * (N : ℝ) := by
    have hp := lam_mul_pow k
    dsimp [a, N]
    push_cast
    nlinarith [hp, C.rPos]
  have hsub := regSites_subset_grid_ball C k
  have hbox := grid_ball_ncard_le a (4 * C.r) N ha hscale
  have hfinite : (Objects.CorrectedEvent.grid a ∩ ball 0 (4 * C.r)).Finite :=
    (Finset.finite_toSet
      ((Finset.Icc (-(N : ℤ)) N).product (Finset.Icc (-(N : ℤ)) N))).image _
      |>.subset (by simpa [Finset.coe_product] using
        grid_ball_subset_box a (4 * C.r) N ha hscale)
  have hfirst : (Objects.CorrectedEvent.regSites C k).ncard ≤ (Objects.CorrectedEvent.grid a ∩ ball 0 (4 * C.r)).ncard := by
    exact Set.ncard_le_ncard (by simpa [a] using hsub) hfinite
  calc
    (Objects.CorrectedEvent.regSites C k).ncard ≤ (Objects.CorrectedEvent.grid a ∩ ball 0 (4 * C.r)).ncard := hfirst
    _ ≤ (2 * N + 1) ^ 2 := hbox
    _ ≤ 1089 * 4 ^ k := by
      dsimp [N]
      have hpow : 4 ^ k = (2 ^ k) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow, pow_two]
      rw [hpow]
      have hx : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      nlinarith

theorem regSites_countable (C : Objects.CorrectedEvent.Constants) (k : ℕ) :
    (Objects.CorrectedEvent.regSites C k).Countable := by
  apply (Set.countable_range
    (latticePoint (Objects.CorrectedEvent.lam k * C.r / 4))).mono
  intro z hz
  obtain ⟨m, n, hmn⟩ := hz.1
  refine ⟨(m, n), ?_⟩
  simpa [latticePoint] using hmn.symm


end SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability
