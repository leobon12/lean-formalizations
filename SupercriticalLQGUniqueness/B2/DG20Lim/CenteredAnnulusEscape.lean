import SupercriticalLQGUniqueness.B2.DG20Lim.AcrossEscape
import SupercriticalLQGUniqueness.B2.DG20Lim.CenteredCircleScale

 

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

private theorem centered_pair_nested (r : ℚ) (hr : 0 < r) :
    (centeredOuterCircle 0 0 r hr).SurroundsCircle
      (centeredInnerCircle 0 0 r hr) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  constructor
  · dsimp [centeredOuterCircle]
    positivity
  · intro w hw
    have hdist : dist w (0 : ℂ) ≤ (r : ℝ) := by
      simpa only [RatCircle.closedDisk, RatCircle.center, centeredInnerCircle,
        Rat.cast_zero,
        show Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) by rfl]
        using (mem_closedBall.mp hw)
    change w ∈ ball
      (centeredOuterCircle 0 0 r hr).center
      ((centeredOuterCircle 0 0 r hr).radius : ℝ)
    apply mem_ball.mpr
    simp only [RatCircle.center, centeredOuterCircle, Rat.cast_zero,
      show Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) by rfl,
      Rat.cast_mul, Rat.cast_ofNat]
    linarith

theorem RData.pointwise_escape_of_large_centered_annuli
    (R : RData)
    (hlarge : ∀ N : ℕ, ∃ r : {r : ℚ // 1 < r},
      (N : ℝ) < (r : ℚ) ∧
      ENNReal.ofReal ((N : ℝ) + 1) ≤ R.across
        (centeredInnerCircle 0 0 r.1 (lt_trans zero_lt_one r.property))
        (centeredOuterCircle 0 0 r.1 (lt_trans zero_lt_one r.property)))
    (u : ℂ) (T : ℝ≥0∞) (hT : T ≠ ∞) :
    ∃ S : ℝ, ∀ v : ℂ, S ≤ dist v 0 → T ≤ R.DfromR u v := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (dist u 0) T.toReal)
  obtain ⟨r, hrN, hcost⟩ := hlarge N
  let hr : 0 < r.1 := lt_trans zero_lt_one r.property
  let Z := centeredInnerCircle 0 0 r.1 hr
  let W := centeredOuterCircle 0 0 r.1 hr
  have hu : u ∈ Z.openDisk := by
    apply mem_ball.mpr
    have hrReal : (N : ℝ) < (r : ℝ) := hrN
    have hu' : dist u 0 < (r : ℝ) :=
      (lt_of_le_of_lt (le_max_left _ _) hN).trans hrReal
    simpa only [Z, RatCircle.openDisk, RatCircle.center,
      centeredInnerCircle, Rat.cast_zero,
      show Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) by rfl]
      using hu'
  have hNested : W.SurroundsCircle Z := centered_pair_nested r.1 hr
  have hTbound : T ≤ ENNReal.ofReal ((N : ℝ) + 1) := by
    rw [← ENNReal.ofReal_toReal hT]
    apply ENNReal.ofReal_le_ofReal
    have htN : T.toReal < (N : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hN
    linarith
  refine ⟨2 * (r : ℝ) + 1, ?_⟩
  intro v hv
  have hvOut : v ∈ W.closedDiskᶜ := by
    have hv' : 2 * (r : ℝ) < dist v 0 := by linarith
    simpa only [W, RatCircle.closedDisk, mem_compl_iff, mem_closedBall,
      not_le, RatCircle.center, centeredOuterCircle, Rat.cast_zero,
      show Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) by rfl,
      Rat.cast_mul, Rat.cast_ofNat]
      using hv'
  exact (hTbound.trans hcost).trans
    (R.across_le_DfromR_of_nested_sides Z W u v hNested hu hvOut)

end SupercriticalLQGUniqueness.B2.DG20Lim
