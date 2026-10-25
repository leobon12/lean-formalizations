import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.ShieldTwoMetric




 


set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

theorem shield_finite_two_metric_all_pairs (C : Objects.CorrectedEvent.Constants)
    (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (D E : LSCMetric)
    (hR : 0 < T.rho * T.r) (W : Set ℂ)
    (hW : ∀ k ∈ Finset.Icc 1 Ksh,
      ball (0 : ℂ) (3 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))) ⊆ W)
    (hBD : BiLipschitz.Barrier.Barrier D) (hBE : BiLipschitz.Barrier.Barrier E)
    (hLD : D.IsLengthSpace) (hLE : E.IsLengthSpace)
    (Cp Ci : ℝ) (hCp : 0 < Cp) (hCi : 0 < Ci)
    (hED : ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal Cp * D p)
    (hDE : ∀ p : ℂ × ℂ, D p ≤ ENNReal.ofReal Ci * E p)
    (hLam : C.lamConst < 1)
    (hRatio : ENNReal.ofReal Cp * ENNReal.ofReal C.lamConst *
      ENNReal.ofReal Ci < 1)
    (hShield : Objects.Excursions.shield C T Ksh D)
    {x y : ℂ} (hx : x ∈ closedBall (0 : ℂ) (3 * (T.rho * T.r)))
    (hy : y ∈ closedBall (0 : ℂ) (3 * (T.rho * T.r))) :
    ∃ (hxW : x ∈ W) (hyW : y ∈ W),
      D.internal W (⟨x, hxW⟩, ⟨y, hyW⟩) = D (x,y) ∧
      E.internal W (⟨x, hxW⟩, ⟨y, hyW⟩) = E (x,y) := by
  obtain ⟨k, hk, hAt⟩ := hShield
  let t : ℝ := 3 * 8 ^ (Ksh - k) * (T.rho * T.r)
  have hpow : 1 ≤ (8 : ℝ) ^ (Ksh - k) := one_le_pow₀ (by norm_num)
  have ht : 0 < t := by dsimp [t]; positivity
  have hsmall : 3 * (T.rho * T.r) ≤ t := by dsimp [t]; nlinarith
  have hx' : x ∈ closedBall (0 : ℂ) t := by
    rw [mem_closedBall] at hx ⊢
    exact hx.trans hsmall
  have hy' : y ∈ closedBall (0 : ℂ) t := by
    rw [mem_closedBall] at hy ⊢
    exact hy.trans hsmall
  have hWt : ball (0 : ℂ) (3 * t) ⊆ W := hW k hk
  obtain ⟨hDeq, hEeq⟩ := shield_two_metric_all_pairs C D E t ht W hWt
    hBD hBE hLD hLE Cp Ci hCp hCi hED hDE hLam hRatio hAt hx' hy'
  exact ⟨_, _, hDeq, hEeq⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
