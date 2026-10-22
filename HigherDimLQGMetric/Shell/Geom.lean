import HigherDimLQGMetric.Shell.Defs
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Connected spheres and shell geometry on `ℝ^d`

Port of `LQGMetric.TopoCircle.sphere_inter_sphere_nonempty` from circles to Euclidean spheres.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

private theorem rank_Rd_gt_one (hd : 2 ≤ d) :
    1 < Module.rank ℝ (Rd d) := by
  rw [← Module.finrank_eq_rank]
  rw [finrank_euclideanSpace_fin]
  exact_mod_cast (show 1 < d by omega)

/-- A sphere that enters an open ball but does not meet its boundary has its whole closed
ball inside that open ball. -/
theorem closedBall_subset_ball_of_sphere_no_inter (hd : 2 ≤ d) {a b x : Rd d}
    {r s : ℝ} (hr : 0 ≤ r) (hx : x ∈ sphere a r) (hxb : x ∈ ball b s)
    (hdisj : ¬ (sphere a r ∩ sphere b s).Nonempty) : closedBall a r ⊆ ball b s := by
  have hsub : sphere a r ⊆ ball b s ∪ (closedBall b s)ᶜ := by
    intro y hy
    by_cases h : y ∈ ball b s
    · exact Or.inl h
    · right
      intro hcl
      apply hdisj
      refine ⟨y, hy, ?_⟩
      rw [mem_sphere, mem_ball, not_lt] at *
      exact le_antisymm hcl h
  have hs : sphere a r ⊆ ball b s := by
    rcases (isConnected_sphere (rank_Rd_gt_one hd) a hr).isPreconnected.subset_or_subset
        isOpen_ball isClosed_closedBall.isOpen_compl
        (disjoint_compl_right.mono_left ball_subset_closedBall) hsub with h | h
    · exact h
    · exact False.elim (h hx (ball_subset_closedBall hxb))
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  rw [← convexHull_sphere_eq_closedBall a hr]
  exact convexHull_min hs (convex_ball b s)

/-- If a sphere enters a ball but its closed ball is not inside, the two spheres intersect. -/
theorem sphere_inter_sphere_nonempty (hd : 2 ≤ d) {a b x : Rd d} {r s : ℝ}
    (hr : 0 ≤ r) (hnot : ¬ closedBall a r ⊆ ball b s)
    (hx : x ∈ sphere a r) (hxb : x ∈ ball b s) :
    (sphere a r ∩ sphere b s).Nonempty := by
  by_contra h
  exact hnot (closedBall_subset_ball_of_sphere_no_inter hd hr hx hxb h)

/-- A connected set that enters and exits a ball meets its boundary sphere. -/
theorem connected_inter_sphere (K : Set (Rd d)) (hK : IsConnected K)
    {c : Rd d} {r : ℝ} (hin : (K ∩ ball c r).Nonempty)
    (hout : ¬ K ⊆ ball c r) : (K ∩ sphere c r).Nonempty := by
  by_contra hne
  have hsub : K ⊆ ball c r ∪ (closedBall c r)ᶜ := by
    intro y hy
    by_cases h : y ∈ ball c r
    · exact Or.inl h
    · right
      intro hcl
      apply hne
      refine ⟨y, hy, ?_⟩
      rw [mem_sphere, mem_ball, not_lt] at *
      exact le_antisymm hcl h
  rcases hK.isPreconnected.subset_or_subset isOpen_ball
      isClosed_closedBall.isOpen_compl
      (disjoint_compl_right.mono_left ball_subset_closedBall) hsub with h | h
  · exact hout h
  · obtain ⟨x, hx, hxb⟩ := hin
    exact h hx (ball_subset_closedBall hxb)

end HigherDimLQGMetric
