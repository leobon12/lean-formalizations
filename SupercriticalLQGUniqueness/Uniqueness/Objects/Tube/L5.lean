import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Cyc
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.L4




 












set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable {P : TubeParams} {r Asup : ℝ}

section L5

variable (hP : P.Good) (hr : 0 < r) (hA0 : 0 < Asup) (hA : 100 * Asup ≤ P.sp * P.ρ)
include hP hr hA0 hA

 
theorem L5 {Asp : ℝ} (hρAsp : 10 ^ 4 * P.ρ ≤ Asp) {F : ℂ → Prop} (hE : EEvent P r Asp F)
    {Q : ℝ → ℂ} {τ σ δ : ℝ} (hτσ : τ ≤ σ) (hQ : ContinuousOn Q (Icc τ σ))
    (hτ : Q τ ∈ closure (P.nbhd r Asup)) (hσ : Q σ ∈ closure (P.nbhd r Asup))
    (hL2 : Asp * r ≤ dist (Q τ) (Q σ)) (hδ : 0 < δ) (hδs : 2 * δ < P.s r / 2)
    (hjump : ∀ a b, τ ≤ a → b ≤ σ → (∀ t ∈ Icc a b, Q t ∉ P.nbhd r Asup) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (Q s) (Q t) < δ) :
    ∃ k : ℤ, F (P.site r k) ∧
      Objects.TubeChecks.Hit Q (P.nbhd r Asup) τ σ δ (P.s r / 2) (P.s r + Asup * r) (P.uC r k) ∧
      Objects.TubeChecks.Hit Q (P.nbhd r Asup) τ σ δ (P.s r / 2) (P.s r + Asup * r) (P.vC r k) := by
  obtain ⟨j, j', hFj, hFj', hjj', hj'K, -, -, -, -, hxS0, hyS4⟩ :=
    select hP hr hA0 hA hρAsp hE hτ hσ hL2
  set S := P.S8 r Asup j j' with hS
  have hgap : ∀ a b : Fin 8, a ≠ b → ¬ Objects.TubeLoops.adj8 a b → ∀ x ∈ S a, ∀ y ∈ S b,
      P.s r / 2 ≤ dist x y := by
    intro a b hab hadj x hx y hy
    obtain ⟨i, hi, hxi⟩ := mem_S8 hx
    obtain ⟨i', hi', hyi⟩ := mem_S8 hy
    exact gap_G2 hP hr hA0 hA (S8_nonAdj (by omega) (by omega) a b hab hadj i hi i' hi') hxi hyi
  have hVopen : IsOpen (P.nbhd r Asup) := isOpen_thickening
  have C : Objects.TubeLoops.Cyc8 Q (P.nbhd r Asup) S τ σ δ :=
    Objects.TubeChecks.cyc8_of_gap hτσ hδ hQ hVopen (S8_cover hP hr hA0 j j') hδs hgap hjump
  obtain ⟨h01, h21, h23, h43, h07, h67, h65, h45⟩ :=
    S8_neighbours hP hr hA0 hA (j := j) (j' := j') (by omega) (by omega)
  rw [S8_ball_one] at h01 h21
  rw [S8_ball_three] at h23 h43
  rw [S8_ball_seven] at h07 h67
  rw [S8_ball_five] at h65 h45
  rcases Objects.TubeChecks.L5_compose C hxS0 hyS4 hδs hgap (S8_ball_one j j') (S8_ball_three j j')
      (S8_ball_five j j') (S8_ball_seven j j') h01 h21 h23 h43 h07 h67 h65 h45 with
    ⟨hu, hv⟩ | ⟨hv, hu⟩
  · exact ⟨j, hFj, hu, hv⟩
  · exact ⟨j', hFj', hu, hv⟩

 



theorem T55_conditional {Asp : ℝ} (hρAsp : 10 ^ 4 * P.ρ ≤ Asp) {F : ℂ → Prop}
    (hE : EEvent P r Asp F) {Q : ℝ → ℂ} {τ σ Anar N a lam : ℝ} (hτσ : τ ≤ σ)
    (hQ : ContinuousOn Q (Icc τ σ))
    (hτ : Q τ ∈ closure (P.nbhd r Asup)) (hσ : Q σ ∈ closure (P.nbhd r Asup))
    (hL2 : Asp * r ≤ dist (Q τ) (Q σ))
    (hAnar0 : 0 < Anar) (hAnar : 8 * Anar ≤ P.sp * P.ρ) (hN : 0 < N) (ha : 0 < a)
    (hlam0 : 0 < lam) (hlam : 3 * lam < 1)
    (hC6 : ∀ s t, τ ≤ s → s ≤ t → t ≤ σ → (∀ u ∈ Icc s t, Q u ∉ P.nbhd r Asup) →
      (∀ u ∈ Icc s t, Q u ∈ {x : ℂ | (3 / 2) * r < ‖x‖ ∧ ‖x‖ < 3 * r}) →
      dist (Q s) (Q t) ≤ lam⁻¹ * (Anar * r) → (dist (Q s) (Q t) / r) ^ a * N ≤ t - s)
    (hL3 : σ - τ ≤ 3 * lam * Anar ^ a * N) :
    ∃ k : ℤ, F (P.site r k) ∧ ∀ w ∈ ({P.uC r k, P.vC r k} : Set ℂ),
      ∃ s₁ t₁ : ℝ, τ ≤ s₁ ∧ s₁ < t₁ ∧ t₁ ≤ σ ∧
        dist (Q s₁) w = P.s r + Asup * r ∧ dist (Q t₁) w = P.s r + Asup * r ∧
        P.s r / 4 ≤ dist (Q s₁) (Q t₁) ∧
        (∀ t ∈ Icc s₁ t₁, dist (Q t) w < P.s r + (Asup + Anar) * r) ∧
        (∀ t ∈ Ioo s₁ t₁, Q t ∈ P.nbhd r Asup → Q t ∈ ball w (P.s r + Asup * r)) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hsp := hP.sp_le'
  have hsr : P.s r = P.sp * (P.ρ * r) := by unfold s; ring
  have hAr : 0 < Anar * r := mul_pos hAnar0 hr
  have hAnar_s : 8 * (Anar * r) ≤ P.s r := by rw [hsr]; nlinarith
  
  have hloc : ∀ x y, y ∈ closure (P.nbhd r Asup) → dist x y ≤ Anar * r →
      x ∈ {x : ℂ | (3 / 2) * r < ‖x‖ ∧ ‖x‖ < 3 * r} := by
    intro x y hy hxy
    have := near_closure_nbhd hP hr hA hy (δ := Anar * r) (by nlinarith) hxy
    exact ⟨this.1, by linarith [this.2]⟩
  obtain ⟨-, hL4⟩ := L4_of_L3_C6 hQ isOpen_thickening hτ hr hAnar0 hN ha hlam0 hlam hloc hC6 hL3
  have hjump := hjump_of_L4 hr hAnar0 ha hlam0 hlam hL4
  set θ := (3 * lam) ^ (1 / a) with hθ
  have hθ1 : θ < 1 := theta_lt_one hlam0 hlam ha
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg (by linarith) _
  set δ := (1 + θ) / 2 * Anar * r with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδA : δ < Anar * r := by rw [hδdef]; nlinarith
  have hδs : 2 * δ < P.s r / 2 := by linarith
  obtain ⟨k, hFk, hu, hv⟩ := L5 hP hr hA0 hA hρAsp hE hτσ hQ hτ hσ hL2 hδ0 hδs hjump
  refine ⟨k, hFk, ?_⟩
  intro w hw
  have hHit : Objects.TubeChecks.Hit Q (P.nbhd r Asup) τ σ δ (P.s r / 2) (P.s r + Asup * r) w := by
    rcases hw with rfl | rfl
    · exact hu
    · exact hv
  obtain ⟨s₁, t₁, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hHit
  refine ⟨s₁, t₁, h1, h2, h3, h4, h5, by linarith, ?_, h7⟩
  intro t ht
  have := h8 t ht
  nlinarith

end L5

 


theorem N4_of_window {Q : ℝ → ℂ} {w : ℂ} {R a b α β : ℝ} (hQ : ContinuousOn Q (Icc a b))
    (haα : a ≤ α) (hαβ : α < β) (hβb : β ≤ b) (hext : ∀ t ∈ Ioo α β, R < dist (Q t) w)
    (hwin : ∀ t ∈ Ioo a b, Q t ∈ P.nbhd r Asup → Q t ∈ ball w R) :
    ∀ t ∈ Icc α β, Q t ∉ P.nbhd r Asup :=
  Objects.TubeChecks.excursion_endpoints_off isOpen_thickening hQ haα hαβ hβb hext hwin


end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
