import HigherDimLQGMetric.Thm13.Perturbation

/-! Compact-uniform agreement of short localized edges with an ambient limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- Uniform convergence of continuous metric functions gives uniformly
small distances between Euclidean-near pairs on a compact ball. -/
theorem l8_small_metric_on_compact (D : ContMetric d) (R b : ℝ) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      ∀ y ∈ Metric.closedBall (0 : Rd d) R,
        dist x y < r → D.1 (x,y) < b := by
  let K : Set (Rd d) := Metric.closedBall (0 : Rd d) R
  have huc : UniformContinuousOn D.1 (K ×ˢ K) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).uniformContinuousOn_of_continuous
      D.1.continuous.continuousOn
  obtain ⟨r, hr, hδ⟩ := Metric.uniformContinuousOn_iff.1 huc b hb
  refine ⟨r, hr, ?_⟩
  intro x hx y hy hxy
  have hdist : dist (x,y) (x,x) < r := by
    simpa [Prod.dist_eq, dist_comm] using hxy
  have h := hδ (x,y) ⟨hx,hy⟩ (x,x) ⟨hx,hx⟩ hdist
  rw [D.apply_self] at h
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (D.nonneg x y)] using h

/-- A compact inverse modulus gives a uniform boundary gap for every
prelimit. Thus short edges equal the ambient limit uniformly in their
Euclidean endpoints. -/
theorem l8_localEdge_eq_on_short_pairs (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d)
    (hconv : Tendsto
      (fun n => (l8_truncScaledMetric hd hκ ξ (hεs n) g).1)
      atTop (𝓝 D.1))
    (R : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      ∀ y ∈ Metric.closedBall (0 : Rd d) R,
        dist x y < r →
        l8_localEdge hd hκ ξ εs hεs g x y = ENNReal.ofReal (D.1 (x,y)) := by
  let S : ℝ := max R 0 + 2
  have hK (x : Rd d) (hx : x ∈ Metric.closedBall (0 : Rd d) R) :
      x ∈ Metric.closedBall (0 : Rd d) S := by
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    dsimp [S]
    linarith [le_max_left R 0]
  obtain ⟨b, hb, hmod⟩ := l8_common_inverse_modulus
    (fun n => l8_truncScaledMetric hd hκ ξ (hεs n) g) D hconv
    (isCompact_closedBall (0 : Rd d) S) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨r, hr, hsmall⟩ := l8_small_metric_on_compact D R b hb
  refine ⟨r, hr, ?_⟩
  intro x hx y hy hxy
  have hbound : ∀ n : ℕ, ∀ z ∈ frontier (Metric.ball x 1),
      b ≤ (l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (x,z) := by
    intro n z hz
    have hsphere : z ∈ Metric.sphere x 1 := Metric.frontier_ball_subset_sphere hz
    have hxz : dist x z = 1 := by
      simpa only [Metric.mem_sphere, dist_comm] using hsphere
    have hzS : z ∈ Metric.closedBall (0 : Rd d) S := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have htri := dist_triangle z x 0
      rw [dist_zero_right, dist_comm z x, hxz] at htri
      rw [dist_zero_right] at htri
      have hxR : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall] using hx
      dsimp [S]
      linarith [le_max_left R 0]
    by_contra hnot
    have hn := hmod n x (hK x hx) z hzS (lt_of_not_ge hnot)
    linarith
  have hconvpt : Tendsto
      (fun n => (l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (x,y))
      atTop (𝓝 (D.1 (x,y))) :=
    (continuous_eval_const (x,y)).continuousAt.tendsto.comp hconv
  have hshort : ∀ᶠ n in atTop,
      (l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (x,y) < b :=
    hconvpt.eventually (gt_mem_nhds (hsmall x hx y hy hxy))
  exact l8_localEdge_eq_of_boundary_gap hd hκ ξ εs hεs g D x y b
    (Eventually.of_forall hbound) hshort hconvpt

/-- A compact ball sits a positive metric distance inside a larger Euclidean
ball, uniformly in the center. Short ambient connections therefore stay in
the larger ball. -/
theorem l8_internal_eq_ambient_on_short_pairs
    (E : ContMetric d) (hE : E.IsLength) (R : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      ∀ y ∈ Metric.closedBall (0 : Rd d) R,
        dist x y < r →
        E.internal (Metric.ball (0 : Rd d) (max R 0 + 3)) x y =
          ENNReal.ofReal (E.1 (x,y)) := by
  let S : ℝ := max R 0 + 3
  have hS : 0 < S := by dsimp [S]; linarith [le_max_right R 0]
  obtain ⟨b, hb, hmod⟩ := l8_common_inverse_modulus
    (fun _ : ℕ => E) E tendsto_const_nhds
    (isCompact_closedBall (0 : Rd d) S) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨r, hr, hsmall⟩ := l8_small_metric_on_compact E R b hb
  refine ⟨r, hr, ?_⟩
  intro x hx y hy hxy
  have hxS : x ∈ Metric.ball (0 : Rd d) S := by
    rw [Metric.mem_ball, dist_zero_right]
    have hxR : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall] using hx
    dsimp [S]
    linarith [le_max_left R 0]
  have hxSc : x ∈ Metric.closedBall (0 : Rd d) S :=
    Metric.ball_subset_closedBall hxS
  have hbar : ∀ z ∈ frontier (Metric.ball (0 : Rd d) S), b ≤ E.1 (x,z) := by
    intro z hz
    have hsphere : z ∈ Metric.sphere (0 : Rd d) S :=
      Metric.frontier_ball_subset_sphere hz
    have hzS : z ∈ Metric.closedBall (0 : Rd d) S :=
      Metric.sphere_subset_closedBall hsphere
    have hzdist : dist (0 : Rd d) z = S := by
      simpa only [Metric.mem_sphere, dist_comm] using hsphere
    have hxR : dist (0 : Rd d) x ≤ R := by
      simpa only [Metric.mem_closedBall, dist_comm] using hx
    have htri := dist_triangle (0 : Rd d) x z
    have hsep : 1 / 2 ≤ dist x z := by
      rw [hzdist] at htri
      dsimp [S] at htri
      linarith [le_max_left R 0]
    by_contra hnot
    have hnear := hmod 0 x hxSc z hzS (lt_of_not_ge hnot)
    linarith
  have hinf : ENNReal.ofReal b ≤
      Metric.infEDist (E.pt x) (E.pt '' frontier (Metric.ball (0 : Rd d) S)) := by
    apply Metric.le_infEDist.2
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [E.edist_pt]
    exact ENNReal.ofReal_le_ofReal (hbar w hw)
  have hlt : edist (E.pt x) (E.pt y) <
      Metric.infEDist (E.pt x) (E.pt '' frontier (Metric.ball (0 : Rd d) S)) := by
    rw [E.edist_pt]
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (E.nonneg x y)).2
      (hsmall x hx y hy hxy)).trans_le hinf
  exact ((E.internal_eq_of_lt_infEDist_frontier hE Metric.isOpen_ball hxS hlt).2).trans
    (E.edist_pt x y)

end HigherDimLQGMetric
