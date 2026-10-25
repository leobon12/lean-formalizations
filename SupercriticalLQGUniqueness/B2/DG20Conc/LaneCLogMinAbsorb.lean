import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPowerRate
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCB3InputMoment
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTailX0Absorb

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_log_min_eventually_le
    (Qψ : PsiParams) (hε : Qψ.ε₀ < (1 : ℝ) / 100)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → laneCLogMin Qψ K ≤ ζ * K := by
  have hζ3 : 0 < ζ / 3 := by positivity
  obtain ⟨K₃, hK₃⟩ := laneC_sublinear_power_le
    (a := (0 : ℝ)) (C := (3 : ℝ)) (ζ := ζ / 3) (by norm_num) hζ3
  obtain ⟨K₁, hK₁⟩ := laneC_sublinear_power_le
    (a := (0 : ℝ)) (C := (1 : ℝ)) (ζ := ζ / 3) (by norm_num) hζ3
  obtain ⟨Kx, hKx⟩ := laneC_sublinear_power_le
    (a := (1 : ℝ) / 2 + 3 * Qψ.ε₀)
    (C := 2 * Real.log 2) (ζ := ζ / 3) (by linarith) hζ3
  refine ⟨max K₃ (max K₁ Kx), fun K hK => ?_⟩
  have h3 := hK₃ K ((le_max_left _ _).trans hK)
  have h1 := hK₁ K ((le_max_left _ _).trans ((le_max_right _ _).trans hK))
  have hx := hKx K ((le_max_right _ _).trans ((le_max_right _ _).trans hK))
  norm_num at h3 h1
  unfold laneCLogMin
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  apply max_le
  · linarith
  · nlinarith

 

theorem laneC_moment_log_threshold_eventually_le
    (Qψ : PsiParams) (hε : Qψ.ε₀ < (1 : ℝ) / 100)
    {q c₀ c₁ ζ : ℝ} (hq : 0 < q) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hζ : 0 < ζ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      max (laneCLogMin Qψ K)
        (T20B.tailX0 q ((5 : ℝ) ^ K) c₀
          (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀)))) ≤ ζ * K := by
  obtain ⟨K₁, h₁⟩ := laneC_log_min_eventually_le Qψ hε hζ
  obtain ⟨K₂, h₂⟩ := laneC_tailX0_five_pow_eventually_le
    (ε := Qψ.ε₀) hq hc₀ hc₁ hε hζ
  refine ⟨max K₁ K₂, fun K hK => max_le
    (h₁ K ((le_max_left _ _).trans hK))
    (h₂ K ((le_max_right _ _).trans hK))⟩

 
theorem laneC_moment_factor_eventually_le
    (Qψ : PsiParams) (hε : Qψ.ε₀ < (1 : ℝ) / 100)
    {q c₀ c₁ ζ : ℝ} (hq : 0 < q) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hζ : 0 < ζ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      Real.exp (q * max (laneCLogMin Qψ K)
        (T20B.tailX0 q ((5 : ℝ) ^ K) c₀
          (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1 ≤
        Real.exp (ζ * K) + 1 := by
  obtain ⟨K₀, hK₀⟩ := laneC_moment_log_threshold_eventually_le
    Qψ hε hq hc₀ hc₁ (div_pos hζ hq)
  refine ⟨K₀, fun K hK => ?_⟩
  have h := hK₀ K hK
  have hmul : q * max (laneCLogMin Qψ K)
      (T20B.tailX0 q ((5 : ℝ) ^ K) c₀
        (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀)))) ≤ ζ * K := by
    calc
      _ ≤ q * (ζ / q * K) := mul_le_mul_of_nonneg_left h hq.le
      _ = ζ * K := by field_simp
  exact add_le_add (Real.exp_le_exp.mpr hmul) le_rfl

end SupercriticalLQGUniqueness.B2.DG20Conc
