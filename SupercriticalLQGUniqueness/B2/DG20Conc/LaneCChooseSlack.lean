import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCFinalL2Slack

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_exists_source_rate_slacks
    (ξ p η : ℝ) (hp : 0 < p) (hη : 0 < η) :
    ∃ δ ζ ν : ℝ, 0 < δ ∧ 0 < ζ ∧ ζ < 1 ∧ 0 < ν ∧
      ((1 + ζ) * p ^ 2 * ξ ^ 2 + 2 * p * δ) +
        (4 * (ζ / (2 * (1 + ζ)))) * (ν / Real.log 2 + 1) ≤
          p ^ 2 * ξ ^ 2 + 2 * η := by
  let A : ℝ := p ^ 2 * ξ ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let δ : ℝ := η / (8 * p)
  let ζ : ℝ := η / (8 * (A + 4) + η)
  let ν : ℝ := Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 8 * (A + 4) + η := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζ1 : ζ < 1 := by
    dsimp [ζ]
    apply (div_lt_one hden).2
    nlinarith
  have hζden : 0 < 1 + ζ := by linarith
  have hζA : ζ * (A + 4) ≤ η / 8 := by
    dsimp [ζ]
    calc
      η / (8 * (A + 4) + η) * (A + 4) =
          (η * (A + 4)) / (8 * (A + 4) + η) := by ring
      _ ≤ η / 8 := by
        apply (div_le_iff₀ hden).2
        nlinarith [sq_nonneg η]
  have hδeq : 2 * p * δ = η / 4 := by
    dsimp [δ]
    field_simp
    ring
  refine ⟨δ, ζ, ν, hδ, hζ, hζ1, hlog, ?_⟩
  have hratio : ζ / (1 + ζ) ≤ ζ := by
    apply (div_le_iff₀ hζden).2
    nlinarith
  have hνeq : ν / Real.log 2 + 1 = 2 := by
    dsimp [ν]
    field_simp [ne_of_gt hlog]
    norm_num
  rw [hνeq, hδeq]
  have hbound : 4 * (ζ / (2 * (1 + ζ))) * 2 ≤ 4 * ζ := by
    calc
      _ = 4 * (ζ / (1 + ζ)) := by
        field_simp [ne_of_gt hζden]
      _ ≤ 4 * ζ := by gcongr
  dsimp [A] at hζA ⊢
  nlinarith

end SupercriticalLQGUniqueness.B2.DG20Conc
