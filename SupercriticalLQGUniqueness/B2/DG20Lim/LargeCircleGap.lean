import SupercriticalLQGUniqueness.B2.DG20Lim.CenteredAnnulusEscape
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteApproxMidpoints

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.exists_large_circle_gap
    (R : RData)
    (hlarge : ∀ N : ℕ, ∃ r : {r : ℚ // 1 < r},
      (N : ℝ) < (r : ℚ) ∧
      ENNReal.ofReal ((N : ℝ) + 1) ≤ R.across
        (centeredInnerCircle 0 0 r.1 (lt_trans zero_lt_one r.property))
        (centeredOuterCircle 0 0 r.1 (lt_trans zero_lt_one r.property)))
    (u v : ℂ) (hfinite : R.DfromR u v ≠ ∞) :
    ∃ O P : RatCircle, P.SurroundsCircle O ∧ u ∈ O.openDisk ∧
      R.DfromR u v + 1 < R.across O P := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (dist u 0) (R.DfromR u v).toReal)
  obtain ⟨r, hrN, hcost⟩ := hlarge N
  let hr : 0 < r.1 := lt_trans zero_lt_one r.property
  let O := centeredInnerCircle 0 0 r.1 hr
  let P := centeredOuterCircle 0 0 r.1 hr
  have hNested : P.SurroundsCircle O := by
    constructor
    · dsimp [P, centeredOuterCircle]
      positivity
    · intro w hw
      have hdist : dist w (0 : ℂ) ≤ (r.1 : ℝ) := by
        simpa only [RatCircle.closedDisk, RatCircle.center, O,
          centeredInnerCircle, Rat.cast_zero,
          show Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) by rfl]
          using (mem_closedBall.mp hw)
      change w ∈ ball P.center (P.radius : ℝ)
      apply mem_ball.mpr
      simp only [P, RatCircle.center, centeredOuterCircle, Rat.cast_zero,
        show Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) by rfl,
        Rat.cast_mul, Rat.cast_ofNat]
      have hrR : (0 : ℝ) < (r.1 : ℝ) := by exact_mod_cast hr
      linarith
  refine ⟨O, P, hNested, ?_, ?_⟩
  · apply mem_ball.mpr
    have hu' : dist u 0 < (r : ℝ) :=
      (lt_of_le_of_lt (le_max_left _ _) hN).trans hrN
    simpa only [O, RatCircle.openDisk, RatCircle.center,
      centeredInnerCircle, Rat.cast_zero,
      show Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) by rfl] using hu'
  · have hgap : R.DfromR u v + 1 < ENNReal.ofReal ((N : ℝ) + 1) := by
      rw [← ENNReal.ofReal_toReal hfinite,
        ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (ENNReal.toReal_nonneg) (by norm_num)]
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
      have hh := lt_of_le_of_lt (le_max_right _ _) hN
      linarith
    exact hgap.trans_le hcost

end SupercriticalLQGUniqueness.B2.DG20Lim
