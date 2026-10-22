import HigherDimLQGMetric.Coord.LimitTopology
import LQGMetric.Metric.CurveNatural

/-!
# Local realization of short coordinate distances

The main compactness input is `lemmaCC`; this file supplies the confinement
and constant-speed path preparations for MA1 A3(ii).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal NNReal

namespace HigherDimLQGMetric

/-- Compact sets strictly inside an open set have a uniform positive coordinate
distance from its boundary under the common lower modulus. -/
theorem uniform_boundary_barrier
    {X : Type*} [MetricSpace X] (ρ : ℕ → X × X → ℝ)
    (hmod : ∀ L : Set X, IsCompact L → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ L, ∀ v ∈ L,
        ρ n (u, v) < δ → dist u v < ε)
    {K O : Set X} (hK : IsCompact K) (hKO : K ⊆ O) (hO : IsOpen O)
    (hOc : IsCompact (closure O)) :
    ∃ a : ℝ, 0 < a ∧ ∀ n, ∀ x ∈ K, ∀ z ∈ frontier O, a ≤ ρ n (x, z) := by
  rcases (frontier O).eq_empty_or_nonempty with he | hfront
  · refine ⟨1, by positivity, ?_⟩
    simp [he]
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le'
    (Metric.continuous_infDist_pt (frontier O)).continuousOn
    (fun x hx => (isClosed_frontier.notMem_iff_infDist_pos hfront).1
      (by
        intro hxf
        rw [frontier, hO.interior_eq] at hxf
        exact hxf.2 (hKO hx)))
  let L := K ∪ closure O
  have hL : IsCompact L := hK.union hOc
  obtain ⟨δ, hδ, hδmod⟩ := hmod L hL m hm
  refine ⟨δ, hδ, ?_⟩
  intro n x hx z hz
  by_contra hnot
  have hsmall := hδmod n x (Or.inl hx) z
    (Or.inr (frontier_subset_closure hz)) (lt_of_not_ge hnot)
  have hsep : m ≤ dist x z :=
    (hmK x hx).trans (Metric.infDist_le_dist_of_mem hz)
  exact (not_lt_of_ge hsep) hsmall

/-- If a path starting in an open set visits its complement, it visits the frontier. -/
private theorem exists_frontier_of_path_point {X : Type*} [TopologicalSpace X]
    {O : Set X} (hO : IsOpen O) {x y : X} (Q : Path x y) (hx : x ∈ O)
    {t : I} (ht : Q t ∉ O) : ∃ s : I, Q s ∈ frontier O := by
  by_contra h
  simp only [not_exists] at h
  have hsub : range Q ⊆ O := by
    refine (isPreconnected_range Q.continuous).subset_left_of_subset_union hO
      isClosed_closure.isOpen_compl (disjoint_compl_right_iff_subset.2 subset_closure) ?_
      ⟨x, ⟨0, Q.source⟩, hx⟩
    rintro _ ⟨u, rfl⟩
    by_cases hu : Q u ∈ O
    · exact Or.inl hu
    · exact Or.inr fun hcl => h u ⟨hcl, by rwa [hO.interior_eq]⟩
  exact ht (hsub ⟨t, rfl⟩)

/-- A path shorter than the boundary barrier cannot leave the open set. -/
theorem IsLengthCoordinate.path_stays_inside
    {X : Type*} [MetricSpace X] {ρ : X × X → ℝ}
    (hρ : IsLengthCoordinate ρ) {O : Set X} (hO : IsOpen O)
    {x y : X} (hx : x ∈ O) {a : ℝ}
    (hbar : ∀ z ∈ frontier O, a ≤ ρ (x, z))
    (γ : Path (MetricFunSpace.pt ρ hρ.metric x) (MetricFunSpace.pt ρ hρ.metric y))
    (hlen : pathLength γ < ENNReal.ofReal a) :
    ∀ t : I, LQGMetric.metricFunSpaceVal ρ hρ.metric (γ t) ∈ O := by
  let Q : Path x y := γ.map hρ.val_continuous
  intro t
  by_contra hnot
  obtain ⟨s, hs⟩ := exists_frontier_of_path_point hO Q hx hnot
  have hcost := edist_le_pathLength_apply γ s
  have hfirst : ENNReal.ofReal a ≤ edist (MetricFunSpace.pt ρ hρ.metric x) (γ s) := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hbar (Q s) hs)
  exact (not_lt_of_ge (hfirst.trans hcost)) hlen

/-- Constant-speed near minimizers confined by the boundary cost. -/
theorem IsLengthCoordinate.exists_short_path_in
    {X : Type*} [MetricSpace X] {ρ : X × X → ℝ}
    (hρ : IsLengthCoordinate ρ) {O : Set X} (hO : IsOpen O)
    {x y : X} (hx : x ∈ O) {a : ℝ} (ha : 0 < a)
    (hbar : ∀ z ∈ frontier O, a ≤ ρ (x, z))
    (hxy : ρ (x, y) < a / 4)
    {ε : ℝ} (hε : 0 < ε) (hεa : ε ≤ a / 4) :
    ∃ γ : Path (MetricFunSpace.pt ρ hρ.metric x) (MetricFunSpace.pt ρ hρ.metric y),
      pathLength γ ≤ ENNReal.ofReal (ρ (x, y) + ε) ∧
      LipschitzWith (Real.toNNReal a) γ ∧
      ∀ t : I, LQGMetric.metricFunSpaceVal ρ hρ.metric (γ t) ∈ O := by
  let px := MetricFunSpace.pt ρ hρ.metric x
  let py := MetricFunSpace.pt ρ hρ.metric y
  obtain ⟨γ, hγ⟩ := hρ.length px py ε hε
  have hγfin : pathLength γ ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hγ
    exact ENNReal.add_ne_top.mpr ⟨edist_ne_top _ _, ENNReal.ofReal_ne_top⟩
  obtain ⟨γ', hlenEq, -, hlip⟩ := exists_lipschitz_path γ hγfin
  have hρnonneg : 0 ≤ ρ (x, y) := by
    change 0 ≤ dist px py
    exact dist_nonneg
  have hlen : pathLength γ' ≤ ENNReal.ofReal (ρ (x, y) + ε) := by
    rw [hlenEq]
    convert hγ using 1
    rw [edist_dist, ENNReal.ofReal_add hρnonneg hε.le]
    rfl
  have hsmall : ρ (x, y) + ε < a := by linarith
  have hγlt : pathLength γ' < ENNReal.ofReal a :=
    hlen.trans_lt ((ENNReal.ofReal_lt_ofReal_iff ha).2 hsmall)
  have hAle : (pathLength γ).toNNReal ≤ Real.toNNReal a := by
    change (pathLength γ).toNNReal ≤ (ENNReal.ofReal a).toNNReal
    exact ENNReal.toNNReal_mono ENNReal.ofReal_ne_top (hlenEq ▸ hγlt.le)
  refine ⟨γ', hlen, hlip.weaken hAle, ?_⟩
  exact hρ.path_stays_inside hO hx hbar γ' hγlt

/-- The coordinate length of a path is its path length in the metric-function space. -/
theorem pathLength_eq_coordinateLength
    {X : Type*} [MetricSpace X] {ρ : X × X → ℝ}
    (hρ : IsMetricFun ρ) {x y : X}
    (γ : Path (MetricFunSpace.pt ρ hρ x) (MetricFunSpace.pt ρ hρ y)) :
    curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
      (Set.IccExtend zero_le_one
        (fun t : I => LQGMetric.metricFunSpaceVal ρ hρ (γ t))) 0 1 = pathLength γ := by
  change _ = curveLength γ.extend 0 1
  rw [← curveLengthWith_edist]
  unfold curveLengthWith
  apply partitionSup_congr
  intro u v hu huv hv
  have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu, huv.trans hv⟩
  have hv' : v ∈ Icc (0 : ℝ) 1 := ⟨hu.trans huv, hv⟩
  rw [Set.IccExtend_of_mem _ _ hu', Set.IccExtend_of_mem _ _ hv',
    Path.extend_apply _ hu', Path.extend_apply _ hv', edist_dist]
  rfl

/-- The compactness argument for short geodesics in a varying coordinate family.
It also applies to a constant family, yielding a geodesic for each approximant. -/
theorem exists_local_geodesic_of_coordinate_limit
    {X : Type*} [MetricSpace X]
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsLengthCoordinate (ρ n))
    {O L : Set X} (hO : IsOpen O) (hOL : O ⊆ L) (hL : IsCompact L)
    (hconv : TendstoUniformlyOn ρ ρlim atTop (L ×ˢ L))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ u ∈ L, ∀ v ∈ L, ρ n (u, v) < δ → dist u v < ε)
    {x y : X} (hxO : x ∈ O) (hyO : y ∈ O)
    {a : ℝ} (ha : 0 < a)
    (hbar : ∀ n, ∀ z ∈ frontier O, a ≤ ρ n (x, z))
    (hshort : ∀ n, ρ n (x, y) < a / 4) :
    ∃ Q : I →ᵇ X, (∀ t, Q t ∈ L) ∧ Q 0 = x ∧ Q 1 = y ∧
      curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1 ≤ ENNReal.ofReal (ρlim (x, y)) := by
  let ε : ℕ → ℝ := fun n => min (a / 4) (1 / ((n : ℝ) + 1))
  have hεpos (n : ℕ) : 0 < ε n := lt_min (by positivity) (by positivity)
  have hεa (n : ℕ) : ε n ≤ a / 4 := min_le_left _ _
  choose γ hγlen hγlip hγO using fun n =>
    (hρ n).exists_short_path_in hO hxO ha (hbar n) (hshort n) (hεpos n) (hεa n)
  let P : ℕ → I →ᵇ X := fun n =>
    mkOfCompact ((γ n).map (hρ n).val_continuous).toContinuousMap
  have hPL : ∀ n t, P n t ∈ L := fun n t => hOL (hγO n t)
  have hspeed : ∀ n : ℕ, ∀ s t : I,
      ρ n (P n s, P n t) ≤ a * dist s t := by
    intro n s t
    have h := (hγlip n).dist_le_mul s t
    change ρ n (P n s, P n t) ≤ (Real.toNNReal a : ℝ) * dist s t at h
    simpa [Real.coe_toNNReal', max_eq_left ha.le] using h
  obtain ⟨Q, hQL, φ, hφ, hPconv, _, hQlen, _⟩ :=
    lemmaCC zero_le_one hL ρ ρlim
      (fun n => (hρ n).continuous.continuousOn) hconv a P hPL hmod hspeed
  have hP0 (n : ℕ) : P n 0 = x := by
    change LQGMetric.metricFunSpaceVal (ρ n) (hρ n).metric (γ n 0) = x
    rw [(γ n).source]
    rfl
  have hP1 (n : ℕ) : P n 1 = y := by
    change LQGMetric.metricFunSpaceVal (ρ n) (hρ n).metric (γ n 1) = y
    rw [(γ n).target]
    rfl
  have hQ0 : Q 0 = x :=
    tendsto_nhds_unique (hPconv.tendsto_at 0) (by simp [hP0])
  have hQ1 : Q 1 = y :=
    tendsto_nhds_unique (hPconv.tendsto_at 1) (by simp [hP1])
  have hρpt : Tendsto (fun n => ρ n (x, y)) atTop (𝓝 (ρlim (x, y))) :=
    hconv.tendsto_at (⟨hOL hxO, hOL hyO⟩)
  have hεlim : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun n : ℕ => min (a / 4) (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (min (a / 4) (0 : ℝ))) := tendsto_const_nhds.min h1
    simpa [ε, min_eq_right (by linarith : (0 : ℝ) ≤ a / 4)] using h2
  have hcostlim : Tendsto
      (fun n => ENNReal.ofReal (ρ (φ n) (x, y) + ε (φ n))) atTop
      (𝓝 (ENNReal.ofReal (ρlim (x, y)))) := by
    have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
    simpa using ENNReal.tendsto_ofReal ((hρpt.comp hφtop).add (hεlim.comp hφtop))
  have hPlen (n : ℕ) :
      curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
        (Set.IccExtend zero_le_one (P n)) 0 1 = pathLength (γ n) := by
    convert pathLength_eq_coordinateLength (hρ n).metric (γ n) using 1
    rfl
  have hbound : ∀ n,
      curveLengthWith (fun u v => ENNReal.ofReal (ρ (φ n) (u, v)))
        (Set.IccExtend zero_le_one (P (φ n))) 0 1 ≤
      ENNReal.ofReal (ρ (φ n) (x, y) + ε (φ n)) := by
    intro n
    rw [hPlen]
    exact hγlen (φ n)
  refine ⟨Q, hQL, hQ0, hQ1, ?_⟩
  calc
    curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1
        ≤ liminf (fun n => curveLengthWith
            (fun u v => ENNReal.ofReal (ρ (φ n) (u, v)))
            (Set.IccExtend zero_le_one (P (φ n))) 0 1) atTop :=
          hQlen le_rfl zero_le_one le_rfl
    _ ≤ liminf (fun n => ENNReal.ofReal (ρ (φ n) (x, y) + ε (φ n))) atTop :=
          Filter.liminf_le_liminf (Eventually.of_forall hbound)
    _ = ENNReal.ofReal (ρlim (x, y)) := hcostlim.liminf_eq

/-- Part (ii) for an approximating coordinate. -/
theorem lemma22ii_approximant
    {X : Type*} [MetricSpace X]
    (ρ : ℕ → X × X → ℝ) (hρ : ∀ n, IsLengthCoordinate (ρ n))
    {O L : Set X} (hO : IsOpen O) (hOL : O ⊆ L) (hL : IsCompact L)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ u ∈ L, ∀ v ∈ L, ρ n (u, v) < δ → dist u v < ε)
    {x y : X} (hxO : x ∈ O) (hyO : y ∈ O)
    {a : ℝ} (ha : 0 < a)
    (hbar : ∀ n, ∀ z ∈ frontier O, a ≤ ρ n (x, z))
    (n : ℕ) (hshort : ρ n (x, y) < a / 4) :
    ∃ Q : I →ᵇ X, (∀ t, Q t ∈ L) ∧ Q 0 = x ∧ Q 1 = y ∧
      curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (ρ n (x, y)) := by
  have hconst : TendstoUniformlyOn (fun _ : ℕ => ρ n) (ρ n) atTop (L ×ˢ L) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with _ p _
    simpa using hε
  obtain ⟨Q, hQL, hQ0, hQ1, hle⟩ :=
    exists_local_geodesic_of_coordinate_limit (fun _ : ℕ => ρ n) (ρ n)
      (fun _ => hρ n) hO hOL hL hconst
      (fun ε hε => by
        obtain ⟨δ, hδ, hδmod⟩ := hmod ε hε
        exact ⟨δ, hδ, fun _ u hu v hv hsmall => hδmod n u hu v hv hsmall⟩)
      hxO hyO ha (fun _ z hz => hbar n z hz) (fun _ => hshort)
  have hdist : ENNReal.ofReal (ρ n (x, y)) ≤
      curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1 := by
    have h := le_curveLengthWith (δ := fun u v => ENNReal.ofReal (ρ n (u, v)))
      (P := Set.IccExtend zero_le_one Q) zero_le_one
    simpa [Set.IccExtend_of_mem, hQ0, hQ1] using h
  exact ⟨Q, hQL, hQ0, hQ1, le_antisymm hle hdist⟩

/-- Part (ii) for the limiting coordinate. -/
theorem lemma22ii_limit
    {X : Type*} [MetricSpace X]
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsLengthCoordinate (ρ n))
    {O L : Set X} (hO : IsOpen O) (hOL : O ⊆ L) (hL : IsCompact L)
    (hconv : TendstoUniformlyOn ρ ρlim atTop (L ×ˢ L))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ u ∈ L, ∀ v ∈ L, ρ n (u, v) < δ → dist u v < ε)
    {x y : X} (hxO : x ∈ O) (hyO : y ∈ O)
    {a : ℝ} (ha : 0 < a)
    (hbar : ∀ n, ∀ z ∈ frontier O, a ≤ ρ n (x, z))
    (hshort : ρlim (x, y) < a / 4) :
    ∃ Q : I →ᵇ X, (∀ t, Q t ∈ L) ∧ Q 0 = x ∧ Q 1 = y ∧
      curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (ρlim (x, y)) := by
  have hxL : x ∈ L := hOL hxO
  have hyL : y ∈ L := hOL hyO
  have hpt : Tendsto (fun n => ρ n (x, y)) atTop (𝓝 (ρlim (x, y))) :=
    hconv.tendsto_at ⟨hxL, hyL⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hpt.eventually (gt_mem_nhds hshort))
  let ρtail : ℕ → X × X → ℝ := fun n => ρ (n + N)
  have htailconv : TendstoUniformlyOn ρtail ρlim atTop (L ×ˢ L) := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    exact (tendsto_add_atTop_nat N).eventually (hconv ε hε)
  have htailmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ u ∈ L, ∀ v ∈ L, ρtail n (u, v) < δ → dist u v < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδmod⟩ := hmod ε hε
    exact ⟨δ, hδ, fun n u hu v hv hs => hδmod (n + N) u hu v hv hs⟩
  obtain ⟨Q, hQL, hQ0, hQ1, hle⟩ :=
    exists_local_geodesic_of_coordinate_limit ρtail ρlim
      (fun n => hρ (n + N)) hO hOL hL htailconv htailmod hxO hyO ha
      (fun n z hz => hbar (n + N) z hz)
      (fun n => hN (n + N) (by omega))
  have hdist : ENNReal.ofReal (ρlim (x, y)) ≤
      curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1 := by
    have h := le_curveLengthWith (δ := fun u v => ENNReal.ofReal (ρlim (u, v)))
      (P := Set.IccExtend zero_le_one Q) zero_le_one
    simpa [Set.IccExtend_of_mem, hQ0, hQ1] using h
  exact ⟨Q, hQL, hQ0, hQ1, le_antisymm hle hdist⟩

/-- Lemma 2.2′(ii) with the positive boundary barrier written explicitly. -/
theorem lemma22ii
    {X : Type*} [MetricSpace X]
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsLengthCoordinate (ρ n))
    (hconv : TendstoLocallyUniformly ρ ρlim atTop)
    (hmod : ∀ L : Set X, IsCompact L → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ L, ∀ v ∈ L,
        ρ n (u, v) < δ → dist u v < ε)
    {K O : Set X} (hKO : K ⊆ O) (hO : IsOpen O)
    (hOc : IsCompact (closure O)) {a : ℝ} (ha : 0 < a)
    (hbar : ∀ n, ∀ x ∈ K, ∀ z ∈ frontier O, a ≤ ρ n (x, z)) :
    (∀ n, ∀ x ∈ K, ∀ y ∈ K, ρ n (x, y) < a / 4 →
      ∃ Q : I →ᵇ X, (∀ t, Q t ∈ closure O) ∧ Q 0 = x ∧ Q 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
          (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (ρ n (x, y))) ∧
    (∀ x ∈ K, ∀ y ∈ K, ρlim (x, y) < a / 4 →
      ∃ Q : I →ᵇ X, (∀ t, Q t ∈ closure O) ∧ Q 0 = x ∧ Q 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
          (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (ρlim (x, y))) := by
  have hconvO : TendstoUniformlyOn ρ ρlim atTop
      (closure O ×ˢ closure O) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (hOc.prod hOc)).1 hconv.tendstoLocallyUniformlyOn
  have hmodO := hmod (closure O) hOc
  constructor
  · intro n x hx y hy hshort
    exact lemma22ii_approximant ρ hρ hO subset_closure hOc hmodO
      (hKO hx) (hKO hy) ha (fun m z hz => hbar m x hx z hz) n hshort
  · intro x hx y hy hshort
    exact lemma22ii_limit ρ ρlim hρ hO subset_closure hOc hconvO hmodO
      (hKO hx) (hKO hy) ha (fun n z hz => hbar n x hx z hz) hshort

end HigherDimLQGMetric
