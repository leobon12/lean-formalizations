import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4Gaussian
import SupercriticalLQGUniqueness.B2.Iface.Statements

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA4_exponent_cancel (ξ Q : ℝ) :
    -(ξ * Q) + (ξ * min ξ Q - (min ξ Q) ^ 2 / 2) =
      -hitExponent ξ Q := by
  by_cases h : ξ ≤ Q
  · rw [min_eq_left h]
    simp only [hitExponent, if_pos h]
    ring
  · have h' : Q < ξ := lt_of_not_ge h
    rw [min_eq_right h'.le]
    simp only [hitExponent, if_neg h]
    ring

 

theorem laneA4_hitExponent_pos_of_QPos
    (hQPos : Iface.DG20ExponentPositive)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hQ : IsLFPPExponent ξ Q) :
    0 < hitExponent (ξ : ℝ) Q :=
  hitExponent_pos ξ.property (hQPos ξ Q hQ)

 


theorem laneA4_exponent_slack
    (ξ Q δ : ℝ) (hξ : 0 ≤ ξ) (hQ : 0 ≤ Q) (hδ : 0 ≤ δ) :
    -(ξ * Q) +
        (ξ * min ξ (Q + δ) - (min ξ (Q + δ)) ^ 2 / 2) ≤
      -hitExponent ξ Q + ξ * δ := by
  let x := min ξ Q
  let y := min ξ (Q + δ)
  have hx0 : 0 ≤ x := le_min hξ hQ
  have hxy : x ≤ y := by
    dsimp [x, y]
    by_cases h : ξ ≤ Q
    · rw [min_eq_left h, min_eq_left (by linarith : ξ ≤ Q + δ)]
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
      by_cases h2 : ξ ≤ Q + δ
      · rw [min_eq_left h2]
        exact (lt_of_not_ge h).le
      · rw [min_eq_right (le_of_lt (lt_of_not_ge h2))]
        linarith
  have hyd : y ≤ x + δ := by
    dsimp [x, y]
    by_cases h : ξ ≤ Q
    · rw [min_eq_left h, min_eq_left (by linarith : ξ ≤ Q + δ)]
      linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
      simpa only using (min_le_right ξ (Q + δ))
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  have hlinear : ξ * y ≤ ξ * x + ξ * δ := by
    nlinarith [mul_nonneg hξ (sub_nonneg.mpr (by linarith : x + δ - y ≥ 0))]
  rw [← laneA4_exponent_cancel ξ Q]
  dsimp [x, y] at hsq hlinear
  nlinarith

end SupercriticalLQGUniqueness.B2.DG20Conc
