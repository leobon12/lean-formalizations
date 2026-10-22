import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Improve.SourceGood
import HigherDimLQGContinuity.Concentration.Core
import HigherDimLQGContinuity.Amplify.Geodesic

/-!
# Pairwise bounds extracted from the fixed source event

The internal-diameter envelope supplies the short-distance estimate used by
net rounding. The lower Hölder envelope supplies its separation threshold.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The source event implies exactly the two pairwise bounds required by
`net_rounding`, with upper constant `2H`. -/
theorem q11_source_rounding_bounds {d : ℕ} {G : ContMetric d}
    {U0 R H σ β w : ℝ} (hG : Q11SourceGood G U0 R H σ β)
    (hR : 2 ≤ R + 1) (hH : 1 ≤ H) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hβ : 0 < β) (hw : 0 < w) :
    (∀ p ∈ closedBall (0 : Rd d) 2, ∀ q ∈ closedBall (0 : Rd d) 2,
      ‖p - q‖ ≤ 1 / 2 → G.1 (p, q) ≤ (2 * H) * ‖p - q‖ ^ σ) ∧
    (∀ p ∈ closedBall (0 : Rd d) 2, ∀ q ∈ closedBall (0 : Rd d) 2,
      w / 2 ≤ ‖p - q‖ → H⁻¹ * (w / 2) ^ β ≤ G.1 (p, q)) := by
  have hball : closedBall (0 : Rd d) 2 ⊆ closedBall 0 (R + 1) :=
    closedBall_subset_closedBall hR
  constructor
  · intro p hp q hq hpq
    exact n4_apply_le_of_diamIn_half (le_trans (by norm_num) hH)
      hσ hσ1 hG.2.2.1 (hball hp) hpq
  · intro p hp q hq hpq
    have hpow : (w / 2) ^ β ≤ ‖p - q‖ ^ β :=
      Real.rpow_le_rpow (by positivity) hpq hβ.le
    exact (mul_le_mul_of_nonneg_left hpow
      (inv_nonneg.mpr (le_trans (by norm_num) hH))).trans
      (hG.2.2.2 p (hball hp) q (hball hq))

/-- The source diameter event gives the endpoint-distance input to the
forcing count for every pair in the radius-two ball. -/
theorem q11_source_pair_le {d : ℕ} {G : ContMetric d}
    {U0 R H σ β : ℝ} (hG : Q11SourceGood G U0 R H σ β)
    (hU0 : 0 ≤ U0) {x y : Rd d}
    (hx : x ∈ closedBall (0 : Rd d) 2)
    (hy : y ∈ closedBall (0 : Rd d) 2) :
    G.1 (x, y) ≤ U0 / 4 := by
  have hsub : closedBall (0 : Rd d) 2 ⊆ closedBall 0 8 :=
    closedBall_subset_closedBall (by norm_num)
  exact p7_apply_le_of_diamIn_le G (hsub hx) (hsub hy)
    (by linarith) hG.1

end HigherDimLQGContinuity
