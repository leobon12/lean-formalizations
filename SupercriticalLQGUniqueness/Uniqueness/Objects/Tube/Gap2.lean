import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Gap




 






set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable {P : TubeParams} {r Asup : ℝ}

 
def NonAdj (K : ℕ) (i j : ℤ) : Prop :=
  ∀ m : ℤ, j - i ≠ 4 * (K * m) - 1 ∧ j - i ≠ 4 * (K * m) ∧ j - i ≠ 4 * (K * m) + 1

section Gap2

variable (hP : P.Good) (hr : 0 < r) (hA0 : 0 < Asup) (hA : 100 * Asup ≤ P.sp * P.ρ)
include hP hr hA0 hA

theorem near_site_of_piece {k : ℤ} {a : ℕ} (ha : a ≤ 2) {x : ℂ} (hx : x ∈ P.piece r Asup k a) :
    dist x (P.site r k) ≤ 5 * (P.ρ * r) := by
  have := dist_piece_site_le hP hr hA0 hA ha hx
  nlinarith [mul_pos hP.ρ_pos hr]

omit hA0 in
 

theorem near_site_of_outA {k : ℤ} {x ℓ : ℂ} (hℓ : ℓ ∈ range (P.outA r k))
    (hxℓ : dist x ℓ < P.w r + Asup * r) : dist x (P.site r k) ≤ 5 * (P.ρ * r) := by
  obtain ⟨hs1, hs2, hs3⟩ := s_le hP hr hA
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  linarith [dist_outA_site hP hr hℓ, dist_triangle x ℓ (P.site r k)]

omit hA0 in
theorem near_site_of_inA {k : ℤ} {x ℓ : ℂ} (hℓ : ℓ ∈ range (P.inA r k))
    (hxℓ : dist x ℓ < P.w r + Asup * r) : dist x (P.site r k) ≤ 5 * (P.ρ * r) := by
  obtain ⟨hs1, hs2, hs3⟩ := s_le hP hr hA
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  linarith [dist_inA_site hP hr hℓ, dist_triangle x ℓ (P.site r k)]

omit hA0 in
theorem far_ge_half_s {x y : ℂ} (h : 100 * (P.ρ * r) ≤ dist x y) : P.s r / 2 ≤ dist x y := by
  obtain ⟨hs1, hs2, hs3⟩ := s_le hP hr hA
  nlinarith [mul_pos hP.ρ_pos hr]

 
theorem gap_succ {k : ℤ} {a b : ℕ} (ha : a < 4) (hb : b < 4) (hab : ¬(a = 3 ∧ b = 0)) {x y : ℂ}
    (hx : x ∈ P.piece r Asup k a) (hy : y ∈ P.piece r Asup (k + 1) b) : P.s r / 2 ≤ dist x y := by
  obtain ⟨hs1, hs2, hs3⟩ := s_le hP hr hA
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hApos : 0 < Asup * r := mul_pos hA0 hr
  have hsp : P.s r = P.sp * (P.ρ * r) := by unfold s; ring
  have hkey : 100 * P.s r ≤ (1 - P.α) * (P.ρ * r) := by rw [hsp]; nlinarith [hP.sp_le]
  have hhalf : P.w r + Asup * r ≤ P.ρ * r / 2 := by linarith
  have e2 : k + 1 + 1 = k + 2 := by ring
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · 
    have hxk := near_site_of_piece hP hr hA0 hA (by omega) hx
    rcases Nat.lt_or_ge b 3 with hb3 | hb3
    · exact far_ge_half_s hP hr hA
        (far_site_site hP hr hxk (near_site_of_piece hP hr hA0 hA (by omega) hy))
    · have hy' : y ∈ P.Λc r Asup (k + 1) := by
        obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
        exact hy
      obtain ⟨⟨ℓ, hℓ, hyℓ⟩, -, -⟩ := mem_Λc' hy'
      rcases hℓ with hℓ | hℓ | hℓ
      · exact far_ge_half_s hP hr hA
          (far_site_site hP hr hxk (near_site_of_outA hP hr hA hℓ hyℓ))
      · rw [range_corridor_eq] at hℓ
        exact far_ge_half_s hP hr hA (far_site_corridor hP hr hxk hℓ (by linarith))
      · have := near_site_of_inA hP hr hA hℓ hyℓ
        rw [e2] at this
        exact far_ge_half_s hP hr hA (far_site_site2 hP hr hxk this)
  · have hx' : x ∈ P.Λc r Asup k := by
      obtain ⟨n, rfl⟩ : ∃ n, a = n + 3 := ⟨a - 3, by omega⟩
      exact hx
    have hb0 : 1 ≤ b := by omega
    obtain ⟨⟨ℓ, hℓ, hxℓ⟩, -, hxu⟩ := mem_Λc' hx'
    rcases hℓ with hℓ | hℓin
    · 
      have hxk := near_site_of_outA hP hr hA hℓ hxℓ
      rcases Nat.lt_or_ge b 3 with hb3 | hb3
      · exact far_ge_half_s hP hr hA
          (far_site_site hP hr hxk (near_site_of_piece hP hr hA0 hA (by omega) hy))
      · have hy' : y ∈ P.Λc r Asup (k + 1) := by
          obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
          exact hy
        obtain ⟨⟨ℓ', hℓ', hyℓ'⟩, -, -⟩ := mem_Λc' hy'
        rcases hℓ' with hℓ' | hℓ' | hℓ'
        · exact far_ge_half_s hP hr hA
            (far_site_site hP hr hxk (near_site_of_outA hP hr hA hℓ' hyℓ'))
        · rw [range_corridor_eq] at hℓ'
          exact far_ge_half_s hP hr hA (far_site_corridor hP hr hxk hℓ' (by linarith))
        · have := near_site_of_inA hP hr hA hℓ' hyℓ'
          rw [e2] at this
          exact far_ge_half_s hP hr hA (far_site_site2 hP hr hxk this)
    · 
      have hℓin' : ℓ ∈ range (P.inA r (k + 1)) ∪ range (P.corridor r k) := by
        rcases hℓin with h | h
        · exact Or.inr h
        · exact Or.inl h
      interval_cases b
      · 
        obtain ⟨hyt, -⟩ := hy
        obtain ⟨ζ, hζ, hyζ⟩ := mem_thickening_iff.mp hyt
        have h2 := dist_ge_sub4 x y ℓ ζ
        rcases block_in_act hP hr hζ hℓin' with h | h
        · rw [dist_comm ζ ℓ] at h
          linarith
        · have hxu' : P.s r + Asup * r ≤ dist x (P.uC r (k + 1)) := not_lt.mp hxu
          have := dist_triangle x ℓ (P.uC r (k + 1))
          linarith
      · 
        have hy' := mem_ball.mp hy
        have h1 := dist_vC_in hP hr hℓin'
        have h2 := dist_ge_sub4 x y ℓ (P.vC r (k + 1))
        rw [dist_comm ℓ (P.vC r (k + 1))] at h2
        have e : (1 - P.α + 3 * P.sp / 4) * (P.ρ * r) = (1 - P.α) * (P.ρ * r) + 3 / 4 * P.s r := by
          rw [hsp]; ring
        linarith
      · 
        have hy' : y ∈ P.Λc r Asup (k + 1) := hy
        obtain ⟨⟨ℓ', hℓ', hyℓ'⟩, -, -⟩ := mem_Λc' hy'
        rcases hℓ' with hℓ' | hℓ' | hℓ'
        · have h1 := in_out_act hP hr hℓin' (Or.inl hℓ')
          have h2 := dist_ge_sub4 x y ℓ ℓ'
          linarith
        · have h1 := in_out_act hP hr hℓin' (Or.inr hℓ')
          have h2 := dist_ge_sub4 x y ℓ ℓ'
          linarith
        · have hyk := near_site_of_inA hP hr hA hℓ' hyℓ'
          rcases hℓin with hc | hi
          · rw [range_corridor_eq] at hc
            rw [e2] at hyk
            exact far_ge_half_s hP hr hA (far_corridor_site hP hr hc (by linarith) hyk)
          · have hxk := near_site_of_inA hP hr hA hi hxℓ
            exact far_ge_half_s hP hr hA (far_site_site hP hr hxk hyk)

 

theorem K9_far {k e : ℤ} (he1 : 2 ≤ e) (he2 : e ≤ P.K - 2) {a b : ℕ} {x y : ℂ}
    (hx : x ∈ P.piece r Asup k a) (hy : y ∈ P.piece r Asup (k + e) b) :
    100 * (P.ρ * r) ≤ dist x y := by
  have hK := hP.K_ne
  have hxs := piece_inSector hP hr hA0 hA hx
  have hys := piece_inSector hP hr hA0 hA hy
  have hKp := hP.K_pos
  have h10 := hP.pi_div_K_ge
  have hρ := hP.ρ_pos
  have e1 : P.ω (k + e) - P.ω (k + 1) = 2 * π * ((e : ℝ) - 1) / P.K := by
    rw [ω_sub hK]; push_cast; ring
  have e2 : P.ω (k + e + 1) - P.ω k = 2 * π * ((e : ℝ) + 1) / P.K := by
    rw [ω_sub hK]; push_cast; ring
  have heR1 : (2 : ℝ) ≤ e := by exact_mod_cast he1
  have heR2 : (e : ℝ) ≤ P.K - 2 := by exact_mod_cast he2
  have f1 : 2 * π / P.K ≤ 2 * π * ((e : ℝ) - 1) / P.K := by
    apply div_le_div_of_nonneg_right _ hKp.le
    nlinarith [Real.pi_pos]
  have f2 : 2 * π * ((e : ℝ) + 1) / P.K ≤ 2 * π - 2 * π / P.K := by
    rw [div_le_iff₀ hKp, sub_mul, div_mul_cancel₀ _ hKp.ne']
    nlinarith [Real.pi_pos]
  have f3 : 2 * π / P.K = 2 * (π / P.K) := by ring
  apply far_of_sectors hP hr hxs hys
  · linarith
  · linarith

 

theorem gap_G2 {i j : ℤ} (hij : NonAdj P.K i j) {x y : ℂ} (hx : x ∈ P.X r Asup i)
    (hy : y ∈ P.X r Asup j) : P.s r / 2 ≤ dist x y := by
  have hK := hP.K_ne
  have hKge := hP.K_ge
  have hKZ : (100 : ℤ) ≤ P.K := by exact_mod_cast hKge
  set k := i / 4 with hk
  set a := (i % 4).toNat with ha
  have hxa : x ∈ P.piece r Asup k a := hx
  set k' := j / 4 with hk'
  set b := (j % 4).toNat with hb
  have hyb : y ∈ P.piece r Asup k' b := hy
  have ha4 : a < 4 := by omega
  have hb4 : b < 4 := by omega
  have hi : i = 4 * k + a := by omega
  have hj : j = 4 * k' + b := by omega
  set e := (k' - k) % (P.K : ℤ) with he
  set q := (k' - k) / (P.K : ℤ) with hq
  have he0 : 0 ≤ e := Int.emod_nonneg _ (by omega)
  have he1 : e < P.K := Int.emod_lt_of_pos _ (by omega)
  have hd : k' - k = P.K * q + e := (Int.mul_ediv_add_emod (k' - k) P.K).symm
  obtain ⟨M, hM⟩ : ∃ M, M = (P.K : ℤ) * q := ⟨_, rfl⟩
  have hy' : y ∈ P.piece r Asup (k + e) b := by
    have hk'e : k' = (k + e) + P.K * q := by omega
    rw [hk'e, piece_add_K_mul hK] at hyb
    exact hyb
  have hji : j - i = 4 * M + 4 * e + b - a := by omega
  obtain ⟨h1, h2, h3⟩ := hij q
  rw [← hM] at h1 h2 h3
  rcases (show e = 0 ∨ e = 1 ∨ e = P.K - 1 ∨ (2 ≤ e ∧ e ≤ P.K - 2) by omega) with he' | he' | he' | he'
  · 
    rw [he', add_zero] at hy'
    have hab : 2 ≤ (b : ℤ) - a ∨ 2 ≤ (a : ℤ) - b := by omega
    interval_cases a <;> interval_cases b <;> simp at hab
    · exact gap_same_02 hP hr hA0 hA hxa hy'
    · exact gap_same_03 hP hr hA0 hA hxa hy'
    · exact gap_same_13 hP hr hA0 hA hxa hy'
    · rw [dist_comm]; exact gap_same_02 hP hr hA0 hA hy' hxa
    · rw [dist_comm]; exact gap_same_03 hP hr hA0 hA hy' hxa
    · rw [dist_comm]; exact gap_same_13 hP hr hA0 hA hy' hxa
  · 
    rw [he'] at hy'
    exact gap_succ hP hr hA0 hA ha4 hb4 (by omega) hxa hy'
  · 
    have hy'' : y ∈ P.piece r Asup (k - 1) b := by
      have := piece_add_K_mul (r := r) (Asup := Asup) hK 1 (k - 1) b
      rw [show k - 1 + (P.K : ℤ) * 1 = k + e by rw [he']; ring] at this
      rw [this] at hy'; exact hy'
    have hx' : x ∈ P.piece r Asup (k - 1 + 1) a := by rw [sub_add_cancel]; exact hxa
    obtain ⟨g1, -, -⟩ := hij (q + 1)
    have hM1 : (P.K : ℤ) * (q + 1) = M + P.K := by rw [hM]; ring
    rw [hM1] at g1
    rw [dist_comm]
    exact gap_succ hP hr hA0 hA hb4 ha4 (by omega) hy'' hx'
  · 
    exact far_ge_half_s hP hr hA (K9_far hP hr hA0 hA he'.1 he'.2 hxa hy')

end Gap2

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
