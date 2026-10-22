import HigherDimLQGMetric.Amplify.FiniteProb
import HigherDimLQGMetric.Amplify.Delta

/-! Choosing enough independent trials for each box. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Filter Topology

/-- A fixed positive success probability can be amplified across any finite
number of boxes by taking sufficiently many independent trials. -/
theorem amplify_exists_trial_count (M : ℕ) {pstar p : ℝ}
    (hpstar : 0 < pstar) (hpstar1 : pstar ≤ 1) (hp : p < 1) :
    ∃ N : ℕ, 0 < N ∧
      (M : ℝ) * (1 - pstar / 2) ^ N < (1 - p) / 4 := by
  let q := 1 - pstar / 2
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hlim : Tendsto (fun N : ℕ => (M : ℝ) * q ^ N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (M : ℝ)
  have hη : 0 < (1 - p) / 4 := by linarith
  have hgood : ∀ᶠ N : ℕ in atTop,
      (M : ℝ) * q ^ N < (1 - p) / 4 :=
    hlim.eventually (eventually_lt_nhds hη)
  obtain ⟨N, hN⟩ :=
    (hgood.and (eventually_gt_atTop (0 : ℕ))).exists
  exact ⟨N, hN.2, hN.1⟩

end HigherDimLQGMetric
