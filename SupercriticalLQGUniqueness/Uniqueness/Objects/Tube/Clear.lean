import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Core




 








set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable {P : TubeParams} {r : ℝ}

section Clear

variable (hP : P.Good) (hr : 0 < r)
include hP hr

theorem dist_modMap' (k : ℤ) (ζ ζ' : ℂ) :
    dist (P.modMap r k ζ) (P.modMap r k ζ') = P.ρ * r * dist ζ ζ' :=
  dist_modMap hP.n_norm (mul_pos hP.ρ_pos hr).le k ζ ζ'

 
theorem out_side {k : ℤ} {q : ℂ} (hq : q ∈ range (P.outA r k) ∪ range (P.corridor r k)) :
    ∃ ζ ∈ range (outPath P.sp P.ψv (P.twist k)) ∪ corrOutH (P.twist k), q = P.modMap r k ζ := by
  rcases hq with hq | hq
  · rw [range_outA] at hq
    obtain ⟨ζ, hζ, rfl⟩ := hq
    exact ⟨ζ, Or.inl hζ, rfl⟩
  · rw [range_corridor_eq] at hq
    obtain ⟨h1, h2⟩ := corridor_frame_out hP hr k hq
    exact ⟨_, Or.inr h1, h2.symm⟩

 
theorem in_side {k : ℤ} {p : ℂ} (hp : p ∈ range (P.inA r (k + 1)) ∪ range (P.corridor r k)) :
    ∃ ζ ∈ range (inPath P.α P.sp P.ψu (P.twist (k + 1))) ∪ corrInH (P.twist (k + 1)),
      p = P.modMap r (k + 1) ζ := by
  rcases hp with hp | hp
  · rw [range_inA] at hp
    obtain ⟨ζ, hζ, rfl⟩ := hp
    exact ⟨ζ, Or.inl hζ, rfl⟩
  · rw [range_corridor_eq] at hp
    obtain ⟨h1, h2⟩ := corridor_frame_in hP hr k hp
    exact ⟨_, Or.inr h1, h2.symm⟩

 

theorem in_out_act {k : ℤ} {p q : ℂ} (hp : p ∈ range (P.inA r (k + 1)) ∪ range (P.corridor r k))
    (hq : q ∈ range (P.outA r (k + 1)) ∪ range (P.corridor r (k + 1))) :
    (1 - P.α) * (P.ρ * r) ≤ dist p q := by
  obtain ⟨ζ, hζ, rfl⟩ := in_side hP hr hp
  obtain ⟨ζ', hζ', rfl⟩ := out_side hP hr hq
  rw [dist_modMap' hP hr]
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hΔ : P.twist (k + 1) ∈ Icc (-π) π :=
    ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have key : 1 - P.α ≤ dist ζ ζ' := by
    rcases hζ with hζ | hζ
    · exact in_out hP.α_gt hP.sp_pos.le hP.sp_le_two_thirds hP.u_minus_pos hP.ψv_mem hΔ hζ hζ'
    · have := cin_out hP.sp_pos.le hP.sp_le_two_thirds hΔ hζ hζ'
      linarith [hP.α_gt]
  nlinarith

 
theorem dist_uC_out {k : ℤ} {q : ℂ} (hq : q ∈ range (P.outA r k) ∪ range (P.corridor r k)) :
    (1 + 3 * P.sp / 4 - P.α) * (P.ρ * r) ≤ dist (P.uC r k) q := by
  obtain ⟨ζ', hζ', rfl⟩ := out_side hP hr hq
  unfold uC
  rw [dist_modMap' hP hr]
  have := K7_u (α := P.α) (ψu := P.ψu) (by linarith [hP.α_gt]) hP.sp_pos.le hP.sp_le_two_thirds hζ'
  nlinarith [mul_pos hP.ρ_pos hr]

 
theorem dist_vC_in {k : ℤ} {p : ℂ} (hp : p ∈ range (P.inA r (k + 1)) ∪ range (P.corridor r k)) :
    (1 - P.α + 3 * P.sp / 4) * (P.ρ * r) ≤ dist (P.vC r (k + 1)) p := by
  obtain ⟨ζ, hζ, rfl⟩ := in_side hP hr hp
  unfold vC
  rw [dist_modMap' hP hr]
  have := K7_v hP.u_minus_pos hP.ψv_mem hζ
  nlinarith [mul_pos hP.ρ_pos hr]

 
theorem dist_uC_vC (k : ℤ) : (1 - P.α) * (P.ρ * r) ≤ dist (P.uC r k) (P.vC r k) := by
  unfold uC vC
  rw [dist_modMap' hP hr]
  have := K8 (ψu := P.ψu) (ψv := P.ψv) (by linarith [hP.α_gt] : 0 ≤ P.α)
  nlinarith [mul_pos hP.ρ_pos hr]

 

theorem block_out_act {k : ℤ} {x q : ℂ} (hx : x ∈ P.block r k)
    (hq : q ∈ range (P.outA r k) ∪ range (P.corridor r k)) :
    P.ρ * r / 2 ≤ dist x q ∨ dist q (P.vC r k) ≤ dist q x := by
  obtain ⟨ζ, hζ, rfl⟩ := hx
  obtain ⟨ζ', hζ', rfl⟩ := out_side hP hr hq
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  rcases hζ' with hζ' | hζ'
  · rw [range_outPath] at hζ'
    rcases hζ' with hζ' | hζ'
    · right
      unfold vC
      rw [dist_modMap' hP hr, dist_modMap' hP hr]
      have := K6_o1 hP.sp_pos.le hP.sp_le_two_thirds hζ' hζ
      exact mul_le_mul_of_nonneg_left this hm.le
    · left
      rw [dist_modMap' hP hr]
      have := K5_out (ψv := P.ψv) (Δ := P.twist k) hζ (Or.inl (Or.inl hζ'))
      nlinarith
  · left
    rw [dist_modMap' hP hr]
    have := K5_out (ψv := P.ψv) hζ (Or.inl (Or.inr hζ'))
    nlinarith

 

theorem block_in_act {k : ℤ} {x p : ℂ} (hx : x ∈ P.block r (k + 1))
    (hp : p ∈ range (P.inA r (k + 1)) ∪ range (P.corridor r k)) :
    P.ρ * r / 2 ≤ dist x p ∨ dist p (P.uC r (k + 1)) ≤ dist p x := by
  obtain ⟨ζ, hζ, rfl⟩ := hx
  obtain ⟨ζ', hζ', rfl⟩ := in_side hP hr hp
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  rcases hζ' with hζ' | hζ'
  · rw [range_inPath] at hζ'
    rcases hζ' with hζ' | hζ'
    · left
      rw [dist_modMap' hP hr]
      have := K5_in hP.α_gt hζ hζ'
      nlinarith
    · right
      unfold uC
      rw [dist_modMap' hP hr, dist_modMap' hP hr]
      have := K6_i1 hP.sp_pos.le hP.u_minus_pos hζ' hζ
      exact mul_le_mul_of_nonneg_left this hm.le
  · left
    rw [dist_modMap' hP hr]
    have := K5_out (ψv := P.ψv) (Δ := P.twist (k + 1)) hζ (Or.inr hζ')
    nlinarith

end Clear

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
