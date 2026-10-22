import HigherDimLQGMetric.Coord.LimitMetric
import LQGMetric.Metric.InternalLimitC
import LQGMetric.Metric.LengthSpace

/-!
# Topology of limits of length coordinates

The first-exit barrier turns the compact lower modulus into a global lower bound
for coordinate distances from a fixed point to the complement of a Euclidean ball.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

/-- A length coordinate: the metric topology is the given topology and the metric is a
length metric.  The two continuity clauses explicitly spell out equality of topologies. -/
structure IsLengthCoordinate {X : Type*} [MetricSpace X] (ρ : X × X → ℝ) : Prop where
  metric : IsMetricFun ρ
  pt_continuous : Continuous (MetricFunSpace.pt ρ metric)
  val_continuous : Continuous (LQGMetric.metricFunSpaceVal ρ metric)
  length : IsLengthMetricFun ρ metric

/-- A coordinate metric induces exactly the ambient topology. -/
structure IsCoordinate {X : Type*} [MetricSpace X] (ρ : X × X → ℝ) : Prop where
  metric : IsMetricFun ρ
  pt_continuous : Continuous (MetricFunSpace.pt ρ metric)
  val_continuous : Continuous (LQGMetric.metricFunSpaceVal ρ metric)

theorem IsLengthCoordinate.toIsCoordinate {X : Type*} [MetricSpace X]
    {ρ : X × X → ℝ} (h : IsLengthCoordinate ρ) : IsCoordinate ρ :=
  ⟨h.metric, h.pt_continuous, h.val_continuous⟩

theorem IsCoordinate.continuous {X : Type*} [MetricSpace X]
    {ρ : X × X → ℝ} (h : IsCoordinate ρ) : Continuous ρ := by
  have hdist : Continuous (fun p : X × X =>
      dist (MetricFunSpace.pt ρ h.metric p.1) (MetricFunSpace.pt ρ h.metric p.2)) :=
    (h.pt_continuous.comp continuous_fst).dist
      (h.pt_continuous.comp continuous_snd)
  simpa only [MetricFunSpace.dist_pt] using hdist

theorem IsLengthCoordinate.continuous {X : Type*} [MetricSpace X]
    {ρ : X × X → ℝ} (h : IsLengthCoordinate ρ) : Continuous ρ := by
  have hdist : Continuous (fun p : X × X =>
      dist (MetricFunSpace.pt ρ h.metric p.1) (MetricFunSpace.pt ρ h.metric p.2)) :=
    (h.pt_continuous.comp continuous_fst).dist
      (h.pt_continuous.comp continuous_snd)
  simpa only [MetricFunSpace.dist_pt] using hdist

/-- A length coordinate has a positive first-exit barrier on every compact ball.
This is the global separation step in MA1 A3(i). -/
theorem lengthCoordinate_ball_barrier
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    (ρ : ℕ → X × X → ℝ)
    (hρ : ∀ n, IsLengthCoordinate (ρ n))
    (hmod : ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ K, ∀ v ∈ K,
        ρ n (u, v) < δ → dist u v < ε)
    (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n y, ε ≤ dist x y → δ ≤ ρ n (x, y) := by
  obtain ⟨K, hK, hKmem⟩ := exists_compact_mem_nhds x
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp hKmem
  let s := min (r / 2) ε
  have hs : 0 < s := lt_min (by positivity) hε
  have hsε : s ≤ ε := min_le_right _ _
  have hsr : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hscompact : IsCompact (Metric.closedBall x s) :=
    hK.of_isClosed_subset Metric.isClosed_closedBall
      ((Metric.closedBall_subset_ball hsr).trans hrK)
  obtain ⟨m, hm, hmod'⟩ := hmod (Metric.closedBall x s) hscompact s hs
  refine ⟨m / 2, by positivity, ?_⟩
  intro n y hxy
  by_contra hnot
  have hshort : ρ n (x, y) < m / 2 := lt_of_not_ge hnot
  let M := (hρ n).metric
  let px : MetricFunSpace (ρ n) M := MetricFunSpace.pt (ρ n) M x
  let py : MetricFunSpace (ρ n) M := MetricFunSpace.pt (ρ n) M y
  obtain ⟨γ, hγ⟩ := (hρ n).length px py (m / 2) (by positivity)
  let Q : Path x y := γ.map (hρ n).val_continuous
  have hxball : x ∈ Metric.ball x s := Metric.mem_ball_self hs
  have hyout : y ∉ Metric.ball x s := by
    have hsy : s ≤ dist x y := hsε.trans hxy
    simpa [Metric.mem_ball, dist_comm] using not_lt.mpr hsy
  obtain ⟨t, ht⟩ := exists_mem_frontier_of_path Metric.isOpen_ball Q hxball hyout
  have htSphere : Q t ∈ Metric.sphere x s := Metric.frontier_ball_subset_sphere ht
  have htu : Q t ∈ Metric.closedBall x s := by
    simpa [Metric.mem_closedBall, Metric.mem_sphere] using le_of_eq htSphere
  have hxu : x ∈ Metric.closedBall x s := by simp [Metric.mem_closedBall, hs.le]
  have hcost := (edist_le_pathLength_apply γ t).trans hγ
  rw [edist_dist, edist_dist] at hcost
  change ENNReal.ofReal (ρ n (x, Q t)) ≤
    ENNReal.ofReal (ρ n (x, y)) + ENNReal.ofReal (m / 2) at hcost
  have hnonneg : 0 ≤ ρ n (x, y) := by
    change 0 ≤ dist (MetricFunSpace.pt (ρ n) M x) (MetricFunSpace.pt (ρ n) M y)
    exact dist_nonneg
  rw [← ENNReal.ofReal_add hnonneg (by positivity : 0 ≤ m / 2)] at hcost
  have hcostReal : ρ n (x, Q t) ≤ ρ n (x, y) + m / 2 :=
    (ENNReal.ofReal_le_ofReal_iff (add_nonneg hnonneg (by positivity))).1 hcost
  have hsmall : ρ n (x, Q t) < m := by linarith
  have hnear := hmod' n x hxu (Q t) htu hsmall
  have heq : dist x (Q t) = s := by simpa [Metric.mem_sphere, dist_comm] using htSphere
  exact (lt_irrefl s) (heq ▸ hnear)

/-- Lemma 2.2′(i): the locally uniform limit of length coordinates is a coordinate.
The proof of the inverse topology uses the first-exit barrier above. -/
theorem isCoordinate_limit_of_lengthCoordinates
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsLengthCoordinate (ρ n))
    (hconv : TendstoLocallyUniformly ρ ρlim atTop)
    (hmod : ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ K, ∀ v ∈ K,
        ρ n (u, v) < δ → dist u v < ε) :
    IsCoordinate ρlim := by
  have hc : Continuous ρlim := hconv.continuous
    (Frequently.of_forall fun n => (hρ n).continuous)
  have hpt : ∀ x y, Tendsto (fun n => ρ n (x, y)) atTop (𝓝 (ρlim (x, y))) :=
    fun x y => hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let M := isMetricFun_of_uniformLowerModulus ρ ρlim
    (fun n => (hρ n).metric) hpt hmod
  have hpcont : Continuous (MetricFunSpace.pt ρlim M) := by
    rw [Metric.continuous_iff']
    intro x ε hε
    have ht : Tendsto (fun y => ρlim (y, x)) (𝓝 x) (𝓝 (ρlim (x, x))) :=
      (hc.comp (continuous_id.prodMk continuous_const)).tendsto x
    rw [M.self_eq_zero] at ht
    exact ht.eventually (gt_mem_nhds hε)
  have hvcont : Continuous (LQGMetric.metricFunSpaceVal ρlim M) := by
    rw [Metric.continuous_iff']
    intro a ε hε
    obtain ⟨δ, hδ, hbar⟩ := lengthCoordinate_ball_barrier ρ hρ hmod
      (LQGMetric.metricFunSpaceVal ρlim M a) ε hε
    filter_upwards [Metric.ball_mem_nhds a hδ] with b hb
    have hdist : ρlim (LQGMetric.metricFunSpaceVal ρlim M b,
        LQGMetric.metricFunSpaceVal ρlim M a) < δ := by
      rw [Metric.mem_ball] at hb
      exact hb
    have hb' : ρlim (LQGMetric.metricFunSpaceVal ρlim M a,
        LQGMetric.metricFunSpaceVal ρlim M b) < δ := by
      rw [M.symm]
      exact hdist
    by_contra hbad
    have hfar : ε ≤ dist (LQGMetric.metricFunSpaceVal ρlim M a)
        (LQGMetric.metricFunSpaceVal ρlim M b) := by
      rw [dist_comm]
      exact le_of_not_gt hbad
    have hlim : δ ≤ ρlim (LQGMetric.metricFunSpaceVal ρlim M a,
        LQGMetric.metricFunSpaceVal ρlim M b) :=
      ge_of_tendsto (hpt _ _) (Eventually.of_forall fun n => hbar n _ hfar)
    exact (not_lt_of_ge hlim) hb'
  exact ⟨M, hpcont, hvcont⟩

/-- Complete part (i) of Lemma 2.2′: topology and the shared lower modulus. -/
theorem lemma22i
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsLengthCoordinate (ρ n))
    (hconv : TendstoLocallyUniformly ρ ρlim atTop)
    (hmod : ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ K, ∀ v ∈ K,
        ρ n (u, v) < δ → dist u v < ε) :
    IsCoordinate ρlim ∧
      ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          (∀ n, ∀ u ∈ K, ∀ v ∈ K, ρ n (u, v) < δ → dist u v < ε) ∧
          (∀ u ∈ K, ∀ v ∈ K, ρlim (u, v) < δ → dist u v < ε) := by
  have hpt : ∀ x y, Tendsto (fun n => ρ n (x, y)) atTop (𝓝 (ρlim (x, y))) :=
    fun x y => hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  refine ⟨isCoordinate_limit_of_lengthCoordinates ρ ρlim hρ hconv hmod, ?_⟩
  intro K hK ε hε
  obtain ⟨δ, hδ, hδn⟩ := hmod K hK ε hε
  refine ⟨δ, hδ, hδn, ?_⟩
  intro u hu v hv hsmall
  obtain ⟨n, hn⟩ := ((hpt u v).eventually (gt_mem_nhds hsmall)).exists
  exact hδn n u hu v hv hn

end HigherDimLQGMetric
