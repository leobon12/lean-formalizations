import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Gap2




 







set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable {P : TubeParams} {r Asup : ℝ}

section G1

variable (hP : P.Good) (hr : 0 < r)
include hP hr

omit hP in
theorem near_circle_of_near_site {k : ℤ} {x : ℂ} {e : ℝ} (hx : dist x (P.site r k) ≤ e) :
    |‖x‖ - 2 * r| ≤ e := by
  obtain ⟨h1, h2⟩ := norm_bounds_of_near_site (P := P) hr k hx
  rw [abs_le]; constructor <;> linarith

 
theorem conn_near_circle {k : ℤ} {x : ℂ} (hx : x ∈ P.conn r k) :
    |‖x‖ - 2 * r| ≤ 10 * (P.ρ * r) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  rw [conn_eq] at hx
  rcases hx with (hx | hx) | hx
  · exact (near_circle_of_near_site hr (dist_outA_site hP hr hx)).trans (by linarith)
  · rw [range_corridor_eq] at hx
    have h1 := (corridor_inSector hP hr k hx).norm_ge (by
      have := two_r_cos_ge hP hr; nlinarith [hP.ρ_le])
    have h2 := corridor_norm_le hP hr k hx
    have h3 := two_r_cos_ge hP hr
    rw [abs_le]; constructor <;> linarith
  · exact (near_circle_of_near_site hr (dist_inA_site hP hr hx)).trans (by linarith)

 
theorem tube_near_circle {x : ℂ} (hx : x ∈ P.tube r) :
    |‖x‖ - 2 * r| ≤ 10 * (P.ρ * r) + P.w r := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hw : 0 ≤ P.w r := by
    unfold w; have := hP.wp_pos; have := hP.ρ_pos; positivity
  have hsp : P.s r ≤ P.ρ * r := by unfold s; nlinarith [hP.sp_le', hP.sp_pos]
  have hα1 := hP.α_lt
  simp only [tube, mem_iUnion] at hx
  obtain ⟨k, hx⟩ := hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact (near_circle_of_near_site hr (dist_block_site hP hr hx)).trans (by linarith)
  · have h1 := mem_ball.mp hx
    have h2 := dist_uC_site hP hr k
    have h3 : dist x (P.site r k) ≤ 2 * (P.ρ * r) := by
      have := dist_triangle x (P.uC r k) (P.site r k); nlinarith
    exact (near_circle_of_near_site hr h3).trans (by linarith)
  · have h1 := mem_ball.mp hx
    have h2 := dist_vC_site hP hr k
    have h3 : dist x (P.site r k) ≤ 2 * (P.ρ * r) := by
      have := dist_triangle x (P.vC r k) (P.site r k); linarith
    exact (near_circle_of_near_site hr h3).trans (by linarith)
  · obtain ⟨ℓ, hℓ, hxℓ⟩ := mem_thickening_iff.mp hx
    have h1 := conn_near_circle hP hr hℓ
    have h2 := norm_gap_le_dist x ℓ
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

 
theorem closure_nbhd_near_circle (hA : 100 * Asup ≤ P.sp * P.ρ) {x : ℂ}
    (hx : x ∈ closure (P.nbhd r Asup)) : |‖x‖ - 2 * r| ≤ 11 * (P.ρ * r) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  obtain ⟨hs1, hs2, hs3⟩ := s_le hP hr hA
  have hclosed : IsClosed {x : ℂ | |‖x‖ - 2 * r| ≤ 11 * (P.ρ * r)} :=
    isClosed_le (by fun_prop) continuous_const
  have hsub : P.nbhd r Asup ⊆ {x : ℂ | |‖x‖ - 2 * r| ≤ 11 * (P.ρ * r)} := by
    intro y hy
    obtain ⟨u, hu, hyu⟩ := mem_thickening_iff.mp hy
    have h1 := tube_near_circle hP hr hu
    have h2 := norm_gap_le_dist y u
    show |‖y‖ - 2 * r| ≤ 11 * (P.ρ * r)
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  exact hclosed.closure_subset_iff.mpr hsub hx

 
theorem closure_nbhd_subset (hA : 100 * Asup ≤ P.sp * P.ρ) :
    closure (P.nbhd r Asup) ⊆ {x : ℂ | (199 / 100) * r < ‖x‖ ∧ ‖x‖ < (201 / 100) * r} := by
  intro x hx
  have h := closure_nbhd_near_circle hP hr hA hx
  have hρ := hP.ρ_le
  rw [abs_le] at h
  constructor <;> nlinarith [hP.ρ_pos]

omit hP in
 
theorem closure_tube_subset_nbhd (hA0 : 0 < Asup) : closure (P.tube r) ⊆ P.nbhd r Asup :=
  closure_subset_thickening (mul_pos hA0 hr) _

 

theorem near_closure_nbhd (hA : 100 * Asup ≤ P.sp * P.ρ) {x y : ℂ}
    (hy : y ∈ closure (P.nbhd r Asup)) {δ : ℝ} (hδ : δ ≤ P.ρ * r) (hxy : dist x y ≤ δ) :
    (3 / 2) * r < ‖x‖ ∧ ‖x‖ < (5 / 2) * r := by
  have h := closure_nbhd_near_circle hP hr hA hy
  have h2 := norm_gap_le_dist x y
  have hρ := hP.ρ_le
  rw [abs_le] at h h2
  constructor <;> nlinarith [hP.ρ_pos]

end G1

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
