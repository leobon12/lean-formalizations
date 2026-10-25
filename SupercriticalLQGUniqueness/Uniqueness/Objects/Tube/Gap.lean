import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Clear




 









set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable {P : TubeParams} {r Asup : ℝ}

 
theorem dist_ge_sub4 (x y p q : ℂ) : dist p q - dist x p - dist y q ≤ dist x y := by
  have h1 := dist_triangle p x q
  have h2 := dist_triangle x y q
  rw [dist_comm p x] at h1
  linarith

theorem mem_Λc' {k : ℤ} {x : ℂ} (hx : x ∈ P.Λc r Asup k) :
    (∃ ℓ, (ℓ ∈ range (P.outA r k) ∨ ℓ ∈ range (P.corridor r k) ∨ ℓ ∈ range (P.inA r (k + 1))) ∧
      dist x ℓ < P.w r + Asup * r) ∧ x ∉ P.βv r Asup k ∧ x ∉ P.βu r Asup (k + 1) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨ℓ, hℓ, hxℓ⟩ := mem_thickening_iff.mp h1
  refine ⟨⟨ℓ, ?_, hxℓ⟩, fun h => h2 (Or.inl h), fun h => h2 (Or.inr h)⟩
  rw [conn_eq] at hℓ
  rcases hℓ with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

section Gap

variable (hP : P.Good) (hr : 0 < r) (hA0 : 0 < Asup) (hA : 100 * Asup ≤ P.sp * P.ρ)
include hP hr hA0 hA

omit hA0 in
 
theorem Λc_inSector {k : ℤ} {x : ℂ} (hx : x ∈ P.Λc r Asup k) :
    InSector x (2 * r - 11 * (P.ρ * r)) (P.ω k - 5 * P.ρ) (P.ω (k + 1) + 5 * P.ρ) := by
  obtain ⟨hs1, hs2, hs3⟩ := s_le hP hr hA
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hω := ω_add_one (P := P) hP.K_ne k
  have hpos : 0 ≤ 2 * π / P.K := by have := hP.K_pos; positivity
  obtain ⟨⟨ℓ, hℓ, hxℓ⟩, -, -⟩ := mem_Λc' hx
  rcases hℓ with hℓ | hℓ | hℓ
  · have := dist_outA_site hP hr hℓ
    have h := inSector_near_site' hP hr (k := k) (x := x)
      (by linarith [dist_triangle x ℓ (P.site r k)])
    exact h.mono le_rfl le_rfl (by rw [hω]; linarith)
  · rw [range_corridor_eq] at hℓ
    have h := inSector_near_corridor hP hr hℓ (x := x) (by linarith)
    exact h.mono le_rfl (by linarith [hP.ρ_pos]) (by linarith [hP.ρ_pos])
  · have := dist_inA_site hP hr hℓ
    have h := inSector_near_site' hP hr (k := k + 1) (x := x)
      (by linarith [dist_triangle x ℓ (P.site r (k + 1))])
    exact h.mono le_rfl (by rw [hω]; linarith [hP.ρ_pos]) le_rfl

 
theorem piece_inSector {k : ℤ} {a : ℕ} {x : ℂ} (hx : x ∈ P.piece r Asup k a) :
    InSector x (2 * r - 11 * (P.ρ * r)) (P.ω k - 5 * P.ρ) (P.ω (k + 1) + 5 * P.ρ) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hω := ω_add_one (P := P) hP.K_ne k
  have hpos : 0 ≤ 2 * π / P.K := by have := hP.K_pos; positivity
  rcases Nat.lt_or_ge a 3 with ha | ha
  · have h1 := dist_piece_site_le hP hr hA0 hA (by omega) hx
    have h := inSector_near_site' hP hr (k := k) (x := x) (by linarith)
    exact h.mono le_rfl le_rfl (by rw [hω]; linarith)
  · have hx' : x ∈ P.Λc r Asup k := by
      obtain ⟨n, rfl⟩ : ∃ n, a = n + 3 := ⟨a - 3, by omega⟩
      exact hx
    exact Λc_inSector hP hr hA hx'

 

theorem gap_same_02 {k : ℤ} {x y : ℂ} (hx : x ∈ P.βu r Asup k) (hy : y ∈ P.βv r Asup k) :
    P.s r / 2 ≤ dist x y := by
  obtain ⟨hs1, hs2, hs3⟩ := s_le hP hr hA
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have h1 := dist_uC_vC hP hr k
  have h2 := dist_ge_sub4 x y (P.uC r k) (P.vC r k)
  have hx' := mem_ball.mp hx
  have hy' := mem_ball.mp hy
  have hApos : 0 < Asup * r := mul_pos hA0 hr
  have hsp : P.s r = P.sp * (P.ρ * r) := by unfold s; ring
  have hkey : 100 * P.s r ≤ (1 - P.α) * (P.ρ * r) := by rw [hsp]; nlinarith [hP.sp_le]
  linarith

theorem gap_same_03 {k : ℤ} {x y : ℂ} (hx : x ∈ P.βu r Asup k) (hy : y ∈ P.Λc r Asup k) :
    P.s r / 2 ≤ dist x y := by
  obtain ⟨hs1, hs2, hs3⟩ := s_le hP hr hA
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hApos : 0 < Asup * r := mul_pos hA0 hr
  have hsp : P.s r = P.sp * (P.ρ * r) := by unfold s; ring
  have hkey : 100 * P.s r ≤ (1 - P.α) * (P.ρ * r) := by rw [hsp]; nlinarith [hP.sp_le]
  have e : (1 + 3 * P.sp / 4 - P.α) * (P.ρ * r) = (1 - P.α) * (P.ρ * r) + 3 / 4 * P.s r := by
    rw [hsp]; ring
  have hx' := mem_ball.mp hx
  obtain ⟨⟨ℓ, hℓ, hyℓ⟩, -, -⟩ := mem_Λc' hy
  rcases hℓ with hℓ | hℓ | hℓ
  · have h1 := dist_uC_out hP hr (Or.inl hℓ)
    have h2 := dist_ge_sub4 x y (P.uC r k) ℓ
    linarith
  · have h1 := dist_uC_out hP hr (Or.inr hℓ)
    have h2 := dist_ge_sub4 x y (P.uC r k) ℓ
    linarith
  · have hxk := dist_piece_site_le hP hr hA0 hA (a := 0) (by norm_num) hx
    have hyk : dist y (P.site r (k + 1)) ≤ 5 * (P.ρ * r) := by
      linarith [dist_inA_site hP hr hℓ, dist_triangle y ℓ (P.site r (k + 1))]
    have := far_site_site hP hr (by linarith) hyk
    linarith

theorem gap_same_13 {k : ℤ} {x y : ℂ} (hx : x ∈ P.Ob r Asup k) (hy : y ∈ P.Λc r Asup k) :
    P.s r / 2 ≤ dist x y := by
  obtain ⟨hs1, hs2, hs3⟩ := s_le hP hr hA
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hApos : 0 < Asup * r := mul_pos hA0 hr
  obtain ⟨hxt, hxr⟩ := hx
  obtain ⟨ζ, hζ, hxζ⟩ := mem_thickening_iff.mp hxt
  obtain ⟨⟨ℓ, hℓ, hyℓ⟩, hyv, -⟩ := mem_Λc' hy
  have h2 := dist_ge_sub4 x y ζ ℓ
  rcases hℓ with hℓ | hℓ | hℓ
  · rcases block_out_act hP hr hζ (Or.inl hℓ) with h | h
    · linarith
    · have hyv' : P.s r + Asup * r ≤ dist y (P.vC r k) := not_lt.mp hyv
      have := dist_triangle y ℓ (P.vC r k)
      rw [dist_comm ζ ℓ] at h2
      linarith
  · rcases block_out_act hP hr hζ (Or.inr hℓ) with h | h
    · linarith
    · have hyv' : P.s r + Asup * r ≤ dist y (P.vC r k) := not_lt.mp hyv
      have := dist_triangle y ℓ (P.vC r k)
      rw [dist_comm ζ ℓ] at h2
      linarith
  · have hxk := dist_piece_site_le hP hr hA0 hA (a := 1) (by norm_num) ⟨hxt, hxr⟩
    have hyk : dist y (P.site r (k + 1)) ≤ 5 * (P.ρ * r) := by
      linarith [dist_inA_site hP hr hℓ, dist_triangle y ℓ (P.site r (k + 1))]
    have := far_site_site hP hr (by linarith) hyk
    linarith

end Gap

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
