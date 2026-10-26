import HigherDimLQGMetric.Weak.DetInternal

/-!
# Uniform local agreement on compact sets
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Det

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- On a compact subset of an open set, the internal metric of a locally uniformly convergent
sequence of length metrics agrees with each global metric for sufficiently close endpoints,
uniformly over the endpoints and eventually uniformly in the index. -/
theorem eventually_internal_eq_global_on_compact
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R))
    {U F : Set (Rd d)} (hU : IsOpen U) (hF : IsCompact F) (hFU : F ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F, ∀ y ∈ F,
      dist x y < δ → (Dn n).internal U x y = ENNReal.ofReal ((Dn n).1 (x,y)) := by
  classical
  let X := {x : Rd d // x ∈ F}
  have hlocal (x : X) : ∃ r : ℝ, 0 < r ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ u ∈ ball x.1 r, ∀ v ∈ ball x.1 r,
        (Dn n).internal U u v = ENNReal.ofReal ((Dn n).1 (u,v)) := by
    obtain ⟨r, hr, -, hev⟩ := eventually_internal_eq_on_small_ball Dn D hDn hconv hU
      (hFU x.2)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    exact ⟨r, hr, N, hN⟩
  choose r hr N₀ hN₀ using hlocal
  let c : X → Set (Rd d) := fun x => ball x.1 (r x / 2)
  have hcopen : ∀ x : X, IsOpen (c x) := fun _ => isOpen_ball
  have hcover : F ⊆ ⋃ x : X, c x := by
    intro z hz
    let x : X := ⟨z, hz⟩
    exact Set.mem_iUnion.2 ⟨x, Metric.mem_ball_self (half_pos (hr x))⟩
  obtain ⟨t, ht⟩ := hF.elim_finite_subcover c hcopen hcover
  let cT : {x : X // x ∈ t} → Set (Rd d) := fun x => c x.1
  have hcTopen : ∀ x : {x : X // x ∈ t}, IsOpen (cT x) := fun x => hcopen x.1
  have hcoverT : F ⊆ ⋃ x : {x : X // x ∈ t}, cT x := by
    intro z hz
    rcases Set.mem_iUnion₂.1 (ht hz) with ⟨x, hxt, hzx⟩
    exact Set.mem_iUnion.2 ⟨⟨x, hxt⟩, hzx⟩
  obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric hF hcTopen hcoverT
  let N : ℕ := t.sup N₀
  refine ⟨δ, hδ, N, ?_⟩
  intro n hn x hx y hy hxy
  obtain ⟨i, hi⟩ := hLeb x hx
  have hxi : x ∈ cT i := hi (Metric.mem_ball_self hδ)
  have hyi : y ∈ cT i := hi (Metric.mem_ball.mpr (by simpa [dist_comm] using hxy))
  have hNi : N₀ i.1 ≤ N := by
    dsimp [N]
    exact Finset.le_sup i.2
  have hN := hN₀ i.1 n (hNi.trans hn)
  have hrad : r i.1 / 2 ≤ r i.1 := by linarith [hr i.1]
  exact hN x (Metric.ball_subset_ball hrad hxi) y (Metric.ball_subset_ball hrad hyi)

end HigherDimLFPPAS.Det

