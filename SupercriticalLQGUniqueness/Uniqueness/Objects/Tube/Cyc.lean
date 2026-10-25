import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Select
import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeLoops.Compose




 










set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable {P : TubeParams} {r Asup : ℝ}

 
def lo8 (j j' : ℤ) : Fin 8 → ℤ
  | 0 => 4 * j' + 3
  | 1 => 4 * j
  | 2 => 4 * j + 1
  | 3 => 4 * j + 2
  | 4 => 4 * j + 3
  | 5 => 4 * j'
  | 6 => 4 * j' + 1
  | 7 => 4 * j' + 2

 
def hi8 (K : ℕ) (j j' : ℤ) : Fin 8 → ℤ
  | 0 => 4 * j + 4 * K - 1
  | 1 => 4 * j
  | 2 => 4 * j + 1
  | 3 => 4 * j + 2
  | 4 => 4 * j' - 1
  | 5 => 4 * j'
  | 6 => 4 * j' + 1
  | 7 => 4 * j' + 2

 
def S8 (P : TubeParams) (r Asup : ℝ) (j j' : ℤ) (a : Fin 8) : Set ℂ :=
  ⋃ i ∈ Icc (lo8 j j' a) (hi8 P.K j j' a), P.X r Asup i

 
theorem nonAdj_of_le {K : ℕ} {i i' : ℤ} (h1 : 2 ≤ i' - i) (h2 : i' - i ≤ 4 * K - 2) :
    NonAdj K i i' := by
  intro m
  rcases le_or_gt m 0 with hm | hm
  · have : (K : ℤ) * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hm
    omega
  · have : (K : ℤ) ≤ K * m := le_mul_of_one_le_right (by positivity) (by omega)
    omega

theorem NonAdj.symm {K : ℕ} {i i' : ℤ} (h : NonAdj K i i') : NonAdj K i' i := by
  intro m
  obtain ⟨h1, h2, h3⟩ := h (-m)
  refine ⟨?_, ?_, ?_⟩ <;> intro hc <;> [apply h3; apply h2; apply h1] <;> linarith [hc]

 
theorem S8_nonAdj {K : ℕ} {j j' : ℤ} (hjj' : j + 1 ≤ j') (hj'K : j' ≤ j + K - 1) :
    ∀ a b : Fin 8, a ≠ b → ¬ Objects.TubeLoops.adj8 a b → ∀ i ∈ Icc (lo8 j j' a) (hi8 K j j' a),
      ∀ i' ∈ Icc (lo8 j j' b) (hi8 K j j' b), NonAdj K i i' := by
  intro a b hab hadj i hi i' hi'
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨hi1', hi2'⟩ := hi'
  fin_cases a <;> fin_cases b <;> simp only [lo8, hi8] at hi1 hi2 hi1' hi2' <;>
    first
    | exact absurd rfl hab
    | exact absurd (by decide) hadj
    | exact nonAdj_of_le (by omega) (by omega)
    | exact (nonAdj_of_le (by omega) (by omega)).symm

section Cyc

variable (hP : P.Good) (hr : 0 < r) (hA0 : 0 < Asup) (hA : 100 * Asup ≤ P.sp * P.ρ)
include hP hr hA0 hA

omit hA0 hA in
theorem s_pos' : 0 < P.s r := by
  unfold s; have := hP.sp_pos; have := hP.ρ_pos; positivity

theorem not_mem_of_nonAdj {i i' : ℤ} (h : NonAdj P.K i i') {x : ℂ} (hx : x ∈ P.X r Asup i) :
    x ∉ P.X r Asup i' := by
  intro hx'
  have := gap_G2 hP hr hA0 hA h hx hx'
  rw [dist_self] at this
  linarith [s_pos' hP hr]

omit hP hr hA0 hA in
theorem X_four_mul (k : ℤ) : P.X r Asup (4 * k) = P.piece r Asup k 0 := by
  have := X_four_mul_add P r Asup k 0 (by norm_num)
  simpa using this

omit hP hr hA0 hA in
theorem X_O_excl {k : ℤ} {x : ℂ} (hx : x ∈ P.X r Asup (4 * k + 1)) :
    x ∉ P.X r Asup (4 * k) ∧ x ∉ P.X r Asup (4 * k + 2) := by
  have e1 := X_four_mul_add P r Asup k 1 (by norm_num)
  have e2 := X_four_mul_add P r Asup k 2 (by norm_num)
  push_cast at e1 e2
  rw [e1] at hx
  rw [X_four_mul, e2]
  exact ⟨fun h => hx.2 (Or.inl h), fun h => hx.2 (Or.inr h)⟩

omit hP hr hA0 hA in
theorem X_Λ_excl {k : ℤ} {x : ℂ} (hx : x ∈ P.X r Asup (4 * k + 3)) :
    x ∉ P.X r Asup (4 * k + 2) ∧ x ∉ P.X r Asup (4 * (k + 1)) := by
  have e3 := X_four_mul_add P r Asup k 3 (by norm_num)
  have e2 := X_four_mul_add P r Asup k 2 (by norm_num)
  push_cast at e2 e3
  rw [e3] at hx
  rw [X_four_mul, e2]
  exact ⟨fun h => hx.2 (Or.inl h), fun h => hx.2 (Or.inr h)⟩

omit hA in
 
theorem S8_cover (j j' : ℤ) :
    P.nbhd r Asup = ⋃ a : Fin 8, P.S8 r Asup j j' a := by
  apply Subset.antisymm
  · rw [nbhd_eq_window hP hr hA0 (4 * j)]
    intro x hx
    rw [mem_iUnion₂] at hx
    obtain ⟨i, ⟨hi1, hi2⟩, hxi⟩ := hx
    rw [mem_iUnion]
    have key : ∃ a : Fin 8, i ∈ Icc (lo8 j j' a) (hi8 P.K j j' a) := by
      rcases (show i = 4 * j ∨ i = 4 * j + 1 ∨ i = 4 * j + 2 ∨ (4 * j + 3 ≤ i ∧ i ≤ 4 * j' - 1) ∨
          i = 4 * j' ∨ i = 4 * j' + 1 ∨ i = 4 * j' + 2 ∨ (4 * j' + 3 ≤ i ∧ i ≤ 4 * j + 4 * P.K - 1)
          by omega) with h | h | h | h | h | h | h | h
      · exact ⟨1, by simp only [lo8, hi8]; exact ⟨h.ge, h.le⟩⟩
      · exact ⟨2, by simp only [lo8, hi8]; exact ⟨h.ge, h.le⟩⟩
      · exact ⟨3, by simp only [lo8, hi8]; exact ⟨h.ge, h.le⟩⟩
      · exact ⟨4, by simp only [lo8, hi8]; exact h⟩
      · exact ⟨5, by simp only [lo8, hi8]; exact ⟨h.ge, h.le⟩⟩
      · exact ⟨6, by simp only [lo8, hi8]; exact ⟨h.ge, h.le⟩⟩
      · exact ⟨7, by simp only [lo8, hi8]; exact ⟨h.ge, h.le⟩⟩
      · exact ⟨0, by simp only [lo8, hi8]; exact h⟩
    obtain ⟨a, ha⟩ := key
    exact ⟨a, mem_biUnion ha hxi⟩
  · have hs : 0 < P.s r := s_pos' hP hr
    have hw : 0 < P.w r := by unfold w; have := hP.wp_pos; have := hP.ρ_pos; positivity
    rw [nbhd_eq_iUnion_X hs hw (mul_pos hA0 hr)]
    exact iUnion_subset fun a => iUnion₂_subset fun i _ => subset_iUnion (P.X r Asup) i

omit hP hr hA0 hA in
theorem S8_ball_one (j j' : ℤ) : P.S8 r Asup j j' 1 = ball (P.uC r j) (P.s r + Asup * r) := by
  simp only [S8, lo8, hi8, Icc_self, mem_singleton_iff, iUnion_iUnion_eq_left]
  rw [X_four_mul]; rfl

omit hP hr hA0 hA in
theorem S8_ball_three (j j' : ℤ) : P.S8 r Asup j j' 3 = ball (P.vC r j) (P.s r + Asup * r) := by
  simp only [S8, lo8, hi8, Icc_self, mem_singleton_iff, iUnion_iUnion_eq_left]
  have e2 := X_four_mul_add P r Asup j 2 (by norm_num)
  push_cast at e2
  rw [e2]; rfl

omit hP hr hA0 hA in
theorem S8_ball_five (j j' : ℤ) : P.S8 r Asup j j' 5 = ball (P.uC r j') (P.s r + Asup * r) := by
  simp only [S8, lo8, hi8, Icc_self, mem_singleton_iff, iUnion_iUnion_eq_left]
  rw [X_four_mul]; rfl

omit hP hr hA0 hA in
theorem S8_ball_seven (j j' : ℤ) : P.S8 r Asup j j' 7 = ball (P.vC r j') (P.s r + Asup * r) := by
  simp only [S8, lo8, hi8, Icc_self, mem_singleton_iff, iUnion_iUnion_eq_left]
  have e2 := X_four_mul_add P r Asup j' 2 (by norm_num)
  push_cast at e2
  rw [e2]; rfl

omit hP hr hA0 hA in
theorem mem_S8 {j j' : ℤ} {a : Fin 8} {x : ℂ} (hx : x ∈ P.S8 r Asup j j' a) :
    ∃ i ∈ Icc (lo8 j j' a) (hi8 P.K j j' a), x ∈ P.X r Asup i := by
  unfold S8 at hx; rw [mem_iUnion₂] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, hi, hxi⟩

omit hP hr hA0 hA in
theorem mem_S8_single {j j' : ℤ} {a : Fin 8} {i₀ : ℤ} (hlo : lo8 j j' a = i₀)
    (hhi : hi8 P.K j j' a = i₀) {x : ℂ} (hx : x ∈ P.S8 r Asup j j' a) : x ∈ P.X r Asup i₀ := by
  obtain ⟨i, hi, hxi⟩ := mem_S8 hx
  rw [hlo, hhi] at hi
  have h1 := hi.1
  have h2 := hi.2
  rw [show i = i₀ by omega] at hxi
  exact hxi

 
theorem S8_neighbours {j j' : ℤ} (hjj' : j + 1 ≤ j') (hj'K : j' ≤ j + P.K - 1) :
    (P.S8 r Asup j j' 0 ⊆ (P.S8 r Asup j j' 1)ᶜ) ∧ (P.S8 r Asup j j' 2 ⊆ (P.S8 r Asup j j' 1)ᶜ) ∧
    (P.S8 r Asup j j' 2 ⊆ (P.S8 r Asup j j' 3)ᶜ) ∧ (P.S8 r Asup j j' 4 ⊆ (P.S8 r Asup j j' 3)ᶜ) ∧
    (P.S8 r Asup j j' 0 ⊆ (P.S8 r Asup j j' 7)ᶜ) ∧ (P.S8 r Asup j j' 6 ⊆ (P.S8 r Asup j j' 7)ᶜ) ∧
    (P.S8 r Asup j j' 6 ⊆ (P.S8 r Asup j j' 5)ᶜ) ∧ (P.S8 r Asup j j' 4 ⊆ (P.S8 r Asup j j' 5)ᶜ) := by
  have hK := hP.K_ne
  have hKZ : (100 : ℤ) ≤ P.K := by exact_mod_cast hP.K_ge
  have m1 : ∀ {x : ℂ}, x ∈ P.S8 r Asup j j' 1 → x ∈ P.X r Asup (4 * j) :=
    fun hx => mem_S8_single rfl rfl hx
  have m2 : ∀ {x : ℂ}, x ∈ P.S8 r Asup j j' 2 → x ∈ P.X r Asup (4 * j + 1) :=
    fun hx => mem_S8_single rfl rfl hx
  have m3 : ∀ {x : ℂ}, x ∈ P.S8 r Asup j j' 3 → x ∈ P.X r Asup (4 * j + 2) :=
    fun hx => mem_S8_single rfl rfl hx
  have m5 : ∀ {x : ℂ}, x ∈ P.S8 r Asup j j' 5 → x ∈ P.X r Asup (4 * j') :=
    fun hx => mem_S8_single rfl rfl hx
  have m6 : ∀ {x : ℂ}, x ∈ P.S8 r Asup j j' 6 → x ∈ P.X r Asup (4 * j' + 1) :=
    fun hx => mem_S8_single rfl rfl hx
  have m7 : ∀ {x : ℂ}, x ∈ P.S8 r Asup j j' 7 → x ∈ P.X r Asup (4 * j' + 2) :=
    fun hx => mem_S8_single rfl rfl hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro x hx hx1
    obtain ⟨i, ⟨hi1, hi2⟩, hxi⟩ := mem_S8 hx
    simp only [lo8, hi8] at hi1 hi2
    have hx1' := m1 hx1
    rcases (show i = 4 * j + 4 * P.K - 1 ∨ i ≤ 4 * j + 4 * P.K - 2 by omega) with h | h
    · have e : i = (4 * (j - 1) + 3) + 4 * (P.K * 1) := by rw [h]; ring
      rw [e, X_add_mul hK] at hxi
      have := (X_Λ_excl hxi).2
      rw [sub_add_cancel] at this
      exact this hx1'
    · exact not_mem_of_nonAdj hP hr hA0 hA (nonAdj_of_le (by omega) (by omega)).symm hxi hx1'
  · intro x hx hx1; exact (X_O_excl (m2 hx)).1 (m1 hx1)
  · intro x hx hx3; exact (X_O_excl (m2 hx)).2 (m3 hx3)
  · 
    intro x hx hx3
    obtain ⟨i, ⟨hi1, hi2⟩, hxi⟩ := mem_S8 hx
    simp only [lo8, hi8] at hi1 hi2
    have hx3' := m3 hx3
    rcases (show i = 4 * j + 3 ∨ 4 * j + 4 ≤ i by omega) with h | h
    · rw [h] at hxi; exact (X_Λ_excl hxi).1 hx3'
    · exact not_mem_of_nonAdj hP hr hA0 hA (nonAdj_of_le (by omega) (by omega)).symm hxi hx3'
  · 
    intro x hx hx7
    obtain ⟨i, ⟨hi1, hi2⟩, hxi⟩ := mem_S8 hx
    simp only [lo8, hi8] at hi1 hi2
    have hx7' := m7 hx7
    rcases (show i = 4 * j' + 3 ∨ 4 * j' + 4 ≤ i by omega) with h | h
    · rw [h] at hxi; exact (X_Λ_excl hxi).1 hx7'
    · exact not_mem_of_nonAdj hP hr hA0 hA (nonAdj_of_le (by omega) (by omega)).symm hxi hx7'
  · intro x hx hx7; exact (X_O_excl (m6 hx)).2 (m7 hx7)
  · intro x hx hx5; exact (X_O_excl (m6 hx)).1 (m5 hx5)
  · 
    intro x hx hx5
    obtain ⟨i, ⟨hi1, hi2⟩, hxi⟩ := mem_S8 hx
    simp only [lo8, hi8] at hi1 hi2
    have hx5' := m5 hx5
    rcases (show i = 4 * j' - 1 ∨ i ≤ 4 * j' - 2 by omega) with h | h
    · have e : i = 4 * (j' - 1) + 3 := by rw [h]; ring
      rw [e] at hxi
      have := (X_Λ_excl hxi).2
      rw [sub_add_cancel] at this
      exact this hx5'
    · exact not_mem_of_nonAdj hP hr hA0 hA (nonAdj_of_le (by omega) (by omega)) hxi hx5'

end Cyc

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
