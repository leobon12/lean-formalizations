import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTailX0Powers

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem laneC_tailX0_five_pow_eventually_le
    {q c₀ c₁ ε ζ : ℝ} (hq : 0 < q) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hε : ε < (1 : ℝ) / 100) (hζ : 0 < ζ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      T20B.tailX0 q ((5 : ℝ) ^ K) c₀
        (c₁ / (4 * (K : ℝ) ^ (3 * ε))) ≤ ζ * K := by
  let C₁ : ℝ := (16 * (q + 1) / c₁) ^ 2
  let C₂ : ℝ :=
    (32 * (Real.log (q * c₀ + 1) + Real.log 4) / c₁) ^ ((2 : ℝ) / 3)
  have hζ3 : 0 < ζ / 3 := by positivity
  obtain ⟨Kc, hKc⟩ := laneC_sublinear_power_le
    (a := (0 : ℝ)) (C := (3 : ℝ)) (ζ := ζ / 3) (by norm_num) hζ3
  obtain ⟨K₁, hK₁⟩ := laneC_sublinear_power_le
    (a := 6 * ε) (C := C₁) (ζ := ζ / 3) (by linarith) hζ3
  obtain ⟨K₂, hK₂⟩ := laneC_sublinear_power_le
    (a := (2 : ℝ) / 3 + 2 * ε) (C := C₂) (ζ := ζ / 3)
    (by linarith) hζ3
  refine ⟨max 1 (max Kc (max K₁ K₂)), fun K hK => ?_⟩
  have hKpos : 1 ≤ K := (le_max_left _ _).trans hK
  have hc := hKc K ((le_max_left _ _).trans (le_max_right _ _ |>.trans hK))
  have h1 := hK₁ K ((le_max_left _ _).trans (le_max_right _ _ |>.trans
    (le_max_right _ _ |>.trans hK)))
  have h2 := hK₂ K ((le_max_right _ _).trans (le_max_right _ _ |>.trans
    (le_max_right _ _ |>.trans hK)))
  have htail := laneC_tailX0_five_pow_le_powers
    (ε := ε) hq hc₀ hc₁ K hKpos
  dsimp [C₁, C₂] at h1 h2
  norm_num at hc
  nlinarith

end SupercriticalLQGUniqueness.B2.DG20Conc
