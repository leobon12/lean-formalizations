import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Geom




 









set_option autoImplicit false

noncomputable section

open Complex Set Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

 
theorem good_of_DG (P : TubeParams) {lam Aloc Aendpt : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 10 ^ 100)            
    (hAloc : 3 < Aloc)                                        
    (hα1 : 3 / 4 < P.α) (hα2 : P.α < 1)                       
    (hE0 : 0 < Aendpt) (hE1 : Aendpt ≤ lam * (1 - P.α) ^ 2)   
    (hs1 : Aendpt ≤ P.sp) (hs2 : P.sp ≤ Real.sqrt Aendpt)     
    (hw : P.wp = lam * Aendpt)                                
    (hρ0 : 0 < P.ρ) (hρ2 : P.ρ ≤ 10 * lam ^ 2 / (π ^ 2 * Aloc ^ 2))   
    (hK : P.K = ⌈lam / (Aloc * P.ρ)⌉₊)                        
    (hn : ‖P.n‖ = 1)                                          
    (hψu : P.ψu ∈ Icc (-(π / 2)) (π / 2)) (hψv : P.ψv ∈ Icc (-(π / 2)) (π / 2)) :
    P.Good := by
  have hπ := Real.pi_gt_three
  have hπ4 := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hA0 : 0 < Aloc := by linarith
  have h1α : 0 < 1 - P.α := by linarith
  
  have hq : π ^ 2 * Aloc / (10 * lam) ≤ lam / (Aloc * P.ρ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : P.ρ * (π ^ 2 * Aloc ^ 2) ≤ 10 * lam ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at hρ2; linarith
    nlinarith
  have hbig : (10 : ℝ) ^ 8 ≤ π ^ 2 * Aloc / (10 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    have : lam * 10 ^ 9 ≤ 1 / 10 ^ 91 := by
      have := hlam; nlinarith
    nlinarith
  have hKge : lam / (Aloc * P.ρ) ≤ P.K := by rw [hK]; exact Nat.le_ceil _
  have hKlt : (P.K : ℝ) < lam / (Aloc * P.ρ) + 1 := by rw [hK]; exact Nat.ceil_lt_add_one (by positivity)
  have hKpos : (0 : ℝ) < P.K := by linarith
  have hsqrt : Real.sqrt Aendpt ≤ (1 - P.α) / 100 := by
    calc Real.sqrt Aendpt ≤ Real.sqrt (lam * (1 - P.α) ^ 2) := Real.sqrt_le_sqrt hE1
      _ = Real.sqrt lam * (1 - P.α) := by
          rw [Real.sqrt_mul hlam0.le, Real.sqrt_sq h1α.le]
      _ ≤ (1 / 100) * (1 - P.α) := by
          apply mul_le_mul_of_nonneg_right _ h1α.le
          rw [show (1 / 100 : ℝ) = Real.sqrt ((1 / 100) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
          apply Real.sqrt_le_sqrt
          nlinarith
      _ = (1 - P.α) / 100 := by ring
  refine ⟨hρ0, hα1, hα2, by linarith, by linarith, ?_, ?_, hψu, hψv, hn, ?_, ?_, ?_⟩
  · rw [hw]; positivity
  · rw [hw]; nlinarith
  · linarith
  · 
    have h1 : P.ρ * P.K ≤ P.ρ * (lam / (Aloc * P.ρ) + 1) := by
      apply mul_le_mul_of_nonneg_left hKlt.le hρ0.le
    have h2 : P.ρ * (lam / (Aloc * P.ρ) + 1) = lam / Aloc + P.ρ := by field_simp
    have h3 : lam / Aloc ≤ lam := by
      rw [div_le_iff₀ hA0]; nlinarith
    have h4 : P.ρ ≤ 10 * lam ^ 2 := by
      calc P.ρ ≤ 10 * lam ^ 2 / (π ^ 2 * Aloc ^ 2) := hρ2
        _ ≤ 10 * lam ^ 2 := by
          apply div_le_self (by positivity)
          have hpa : 9 < π * Aloc := by nlinarith
          nlinarith [hpa]
    nlinarith
  · 
    have hK2 : (lam / (Aloc * P.ρ)) ^ 2 ≤ (P.K : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hKge
    rw [div_le_iff₀ (by positivity)]
    have e : (lam / (Aloc * P.ρ)) ^ 2 = lam ^ 2 / (Aloc ^ 2 * P.ρ ^ 2) := by field_simp
    rw [e] at hK2
    have h5 : π ^ 2 ≤ 10 * P.ρ * (lam ^ 2 / (Aloc ^ 2 * P.ρ ^ 2)) := by
      rw [show 10 * P.ρ * (lam ^ 2 / (Aloc ^ 2 * P.ρ ^ 2)) = 10 * lam ^ 2 / (Aloc ^ 2 * P.ρ) by
        field_simp]
      rw [le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hρ2
      nlinarith
    nlinarith

 
theorem small_of_DG (P : TubeParams) {lam Aendpt Anar Asup : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 10 ^ 100) (hα1 : 3 / 4 < P.α) (hE0 : 0 < Aendpt)
    (hs1 : Aendpt ≤ P.sp) (hρ0 : 0 < P.ρ) (hsup0 : 0 < Asup) (hsup : Asup < Anar)
    (hnar : Anar ≤ lam * (1 - P.α) * Aendpt * P.ρ) :
    100 * Asup ≤ P.sp * P.ρ ∧ 8 * Anar ≤ P.sp * P.ρ := by
  have h1 : lam * (1 - P.α) ≤ 1 / 100 := by nlinarith
  have h2 : Anar ≤ (1 / 100) * Aendpt * P.ρ := by
    calc Anar ≤ lam * (1 - P.α) * Aendpt * P.ρ := hnar
      _ ≤ (1 / 100) * Aendpt * P.ρ := by
        apply mul_le_mul_of_nonneg_right _ hρ0.le
        exact mul_le_mul_of_nonneg_right h1 hE0.le
  constructor <;> nlinarith

 
theorem rho_Asp_of_DG {lam ρ Asp : ℝ} (hlam : lam < 1 / 10 ^ 100) (hAsp : 0 < Asp)
    (hρ : ρ < lam * Asp) : 10 ^ 4 * ρ ≤ Asp := by
  nlinarith

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
