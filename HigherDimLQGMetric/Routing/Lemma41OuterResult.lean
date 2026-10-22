import HigherDimLQGMetric.Routing.Lemma41OuterAssembly

/-! Lemma 4.1′ in the configuration's actual outer-annulus coordinate carrier. -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Topology HigherDimLFPP LQGMetric.MetricGeometry BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

/-- Evaluate the second coordinate along curves represented in the first coordinate's metric space. -/
def lemma41_outerCoordinateCost {d : ℕ}
    (ζ : (configOuter d) × (configOuter d) → ℝ) (hζ : IsCoordinate ζ)
    (ζtilde : (configOuter d) × (configOuter d) → ℝ)
    (x y : MetricFunSpace ζ hζ.metric) : ℝ≥0∞ :=
  ENNReal.ofReal (ζtilde
    (LQGMetric.metricFunSpaceVal ζ hζ.metric x,
      LQGMetric.metricFunSpaceVal ζ hζ.metric y))

theorem lemma41_outerCoordinateCost_length {d : ℕ}
    (ζ : (configOuter d) × (configOuter d) → ℝ) (hζ : IsCoordinate ζ)
    (ζtilde : (configOuter d) × (configOuter d) → ℝ)
    (γ : ℝ → configOuter d) (a b : ℝ) :
    curveLengthWith (lemma41_outerCoordinateCost ζ hζ ζtilde)
      (MetricFunSpace.pt ζ hζ.metric ∘ γ) a b =
    curveLengthWith (fun x y : configOuter d => ENNReal.ofReal (ζtilde (x, y)))
      γ a b := by
  rfl

theorem lemma41_outerCoordinateCost_length_repr {d : ℕ}
    (ζ : (configOuter d) × (configOuter d) → ℝ) (hζ : IsCoordinate ζ)
    (ζtilde : (configOuter d) × (configOuter d) → ℝ)
    (σ : ℝ → MetricFunSpace ζ hζ.metric) (a b : ℝ) :
    curveLengthWith (lemma41_outerCoordinateCost ζ hζ ζtilde) σ a b =
    curveLengthWith (fun x y : configOuter d => ENNReal.ofReal (ζtilde (x, y)))
      (LQGMetric.metricFunSpaceVal ζ hζ.metric ∘ σ) a b := by
  rfl

/-- The routed graph in the coordinate metric on `configOuter d`. -/
structure Lemma41OuterRoutingResult {d : ℕ} {δ : ℝ}
    (hd : 1 ≤ d) (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    (T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (E : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (γ : T.edgeSet → ℝ → configOuter d) (a₁ c₃ : ℝ) where
  K : Set (MetricFunSpace ρ hρ.metric)
  C : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) →
    Set (MetricFunSpace ρ hρ.metric)
  σ : T.edgeSet → ℝ → MetricFunSpace ρ hρ.metric
  graph : IsFiniteRectGraph K
  collector : K ⊆ lemma41_outerImage ρ hρ (meshCollector d δ)
  vertex : ∀ v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2),
    lemma41_outerMeshPoint hd hδ hsmall ρ hρ v ∈ K
  Ccompact : ∀ v, IsCompact (C v)
  Cconnected : ∀ v, IsConnected (C v)
  Cvertex : ∀ v, lemma41_outerMeshPoint hd hδ hsmall ρ hρ v ∈ C v
  Cstar : ∀ v, C v ⊆ lemma41_outerMeshStar ρ hρ v
  Cdisjoint : ∀ v w, v ≠ w → Disjoint (C v) (C w)
  partition : K \ (⋃ e, σ e '' Ioo (0 : ℝ) 1) = ⋃ v, C v
  σcontinuous : ∀ e, ContinuousOn (σ e) (Icc 0 1)
  σinjective : ∀ e, InjOn (σ e) (Icc 0 1)
  σK : ∀ e, σ e '' Icc (0 : ℝ) 1 ⊆ K
  σtrace : ∀ e, σ e '' Icc (0 : ℝ) 1 ⊆
    MetricFunSpace.pt ρ hρ.metric '' (γ e '' Icc (0 : ℝ) 1)
  σsubarc : ∀ e, ∃ s t : ℝ, 0 < s ∧ s < t ∧ t < 1 ∧
    σ e = (fun r => MetricFunSpace.pt ρ hρ.metric (γ e (s + (t - s) * r)))
  σbox : ∀ e, σ e '' Icc (0 : ℝ) 1 ⊆ lemma41_outerMeshBox ρ hρ e
  σseparated : ∀ e, a₁ / 2 < dist (σ e 0) (σ e 1)
  σshort : ∀ e, curveLengthWith E (σ e) 0 1 <
    ENNReal.ofReal (c₃ * dist (σ e 0) (σ e 1))
  forcing : ∀ {b : ℝ}, 0 < b →
    (∀ v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2),
      ∀ x ∈ lemma41_outerMeshStar ρ hρ v,
      ∀ y ∈ lemma41_outerMeshStar ρ hρ v, dist x y < b / 8) →
    ∀ {Tlen ℓ : ℝ}, (hTlen : 0 ≤ Tlen) → 0 ≤ ℓ → (hℓT : ℓ ≤ Tlen) →
      ∀ (Q : Icc (0 : ℝ) Tlen →ᵇ MetricFunSpace ρ hρ.metric),
        (∀ u ∈ Icc (0 : ℝ) ℓ, Set.IccExtend hTlen Q u ∈ K) →
        (∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
          internalEDist K (Set.IccExtend hTlen Q s)
            (Set.IccExtend hTlen Q t) = ENNReal.ofReal (t - s)) →
        b / 4 ≤ dist (Set.IccExtend hTlen Q 0)
          (Set.IccExtend hTlen Q ℓ) →
        ∃ e : T.edgeSet,
          TraversesMarkedArc hℓT Q (σ e) ∨
            TraversesMarkedArc hℓT Q (fun r => σ e (1 - r))

/-- The routing theorem for the `U = A_{1/2,5}` coordinate used by configurations. -/
theorem lemma41_outer_routing {d : ℕ} (hd : 3 ≤ d)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (hTconn : T.Connected)
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set (configOuter d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ r, LQGMetric.metricFunSpaceVal ρ hρ.metric (P r) ∈ O) ∧
          pathLength P ≠ ∞)
    (E : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (γ : T.edgeSet → ℝ → configOuter d)
    (hγc : ∀ e, ContinuousOn (γ e) (Icc 0 1))
    (hγi : ∀ e, InjOn (γ e) (Icc 0 1))
    (hγbox : ∀ e, ∀ r ∈ Icc (0 : ℝ) 1,
      (γ e r).1 ∈ centralBox δ
        (Topology.latticePoint δ (lemma41_meshLeft e).1)
        (Topology.latticePoint δ (lemma41_meshRight e).1))
    (hγlen : ∀ e, curveLength (MetricFunSpace.pt ρ hρ.metric ∘ γ e) 0 1 ≠ ∞)
    {a₁ c₂ c₃ : ℝ} (ha₁ : 0 < a₁) (hc₂ : 0 ≤ c₂) (hc₂₃ : c₂ < c₃)
    (hsep : ∀ e, a₁ ≤ ρ (γ e 0, γ e 1))
    (hE : ∀ e, curveLengthWith E (MetricFunSpace.pt ρ hρ.metric ∘ γ e) 0 1 ≤
      ENNReal.ofReal (c₂ * ρ (γ e 0, γ e 1))) :
    Nonempty (Lemma41OuterRoutingResult (by omega : 1 ≤ d) hδ hsmall
      T ρ hρ E γ a₁ c₃) := by
  classical
  letI : Fintype (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    (routingMesh_finite hδ).fintype
  letI : Nontrivial (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    lemma41_routing_mesh_nontrivial (by omega : 1 ≤ d) hδ hsmall
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  have hP : ∀ e : T.edgeSet, ∃ P : Lemma41LocalPiece
      (lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ (lemma41_meshLeft e))
      (lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ (lemma41_meshRight e))
      (lemma41_outerMeshRegL ρ hρ e) (lemma41_outerMeshRegR ρ hρ e)
      (lemma41_outerMeshBox ρ hρ e) E a₁ c₃,
      P.σ '' Icc (0 : ℝ) 1 ⊆
        MetricFunSpace.pt ρ hρ.metric '' (γ e '' Icc (0 : ℝ) 1) ∧
      ∃ s t : ℝ, 0 < s ∧ s < t ∧ t < 1 ∧
        P.σ = (fun r => MetricFunSpace.pt ρ hρ.metric
          (γ e (s + (t - s) * r))) := by
    intro e
    exact lemma41_outer_local_piece hd hδ hsmall
      (lemma41_meshLeft e).property (lemma41_meshRight e).property
      (lemma41_tree_edge_adj hT e) ρ hρ hreal E (γ e)
      (hγc e) (hγi e) (hγbox e) (hγlen e)
      ha₁ hc₂ hc₂₃ (hsep e) (hE e)
  let P : ∀ e : T.edgeSet, Lemma41LocalPiece
      (lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ (lemma41_meshLeft e))
      (lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ (lemma41_meshRight e))
      (lemma41_outerMeshRegL ρ hρ e) (lemma41_outerMeshRegR ρ hρ e)
      (lemma41_outerMeshBox ρ hρ e) E a₁ c₃ := fun e => (hP e).choose
  have htrace : ∀ e, (P e).σ '' Icc (0 : ℝ) 1 ⊆
      MetricFunSpace.pt ρ hρ.metric '' (γ e '' Icc (0 : ℝ) 1) :=
    fun e => (hP e).choose_spec.1
  have hsubarc : ∀ e, ∃ s t : ℝ, 0 < s ∧ s < t ∧ t < 1 ∧
      (P e).σ = (fun r => MetricFunSpace.pt ρ hρ.metric
        (γ e (s + (t - s) * r))) :=
    fun e => (hP e).choose_spec.2
  let K : Set (MetricFunSpace ρ hρ.metric) := ⋃ e : T.edgeSet, (P e).K
  let C : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) →
      Set (MetricFunSpace ρ hρ.metric) :=
    fun v => ⋃ e : T.edgeSet,
      lemma41_side lemma41_meshLeft lemma41_meshRight
        (fun e => (P e).L) (fun e => (P e).R) e v
  let σ : T.edgeSet → ℝ → MetricFunSpace ρ hρ.metric := fun e => (P e).σ
  have hgraph := lemma41_outer_family_graph hd hδ hsmall hT hTconn ρ hρ E a₁ c₃ P
  have hpart := lemma41_outer_family_partition hd hδ hsmall hT hTconn ρ hρ E a₁ c₃ P
  change (∀ v, IsCompact (C v) ∧ IsConnected (C v) ∧
      lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ v ∈ C v ∧
      C v ⊆ lemma41_outerMeshStar ρ hρ v) ∧
    (∀ v w, v ≠ w → Disjoint (C v) (C w)) ∧
    K \ (⋃ e, σ e '' Ioo (0 : ℝ) 1) = ⋃ v, C v at hpart
  refine ⟨⟨K, C, σ, hgraph.1, hgraph.2.1, hgraph.2.2,
    (fun v => (hpart.1 v).1), (fun v => (hpart.1 v).2.1),
    (fun v => (hpart.1 v).2.2.1), (fun v => (hpart.1 v).2.2.2),
    hpart.2.1, hpart.2.2, (fun e => (P e).σcontinuous),
    (fun e => (P e).σinjective), ?_, htrace, hsubarc, (fun e => (P e).σbox),
    (fun e => (P e).σseparated), (fun e => (P e).σshort), ?_⟩⟩
  · intro e x hx
    exact Set.mem_iUnion_of_mem e ((P e).σK hx)
  · intro b hb hdiam Tlen ℓ hTlen hℓ0 hℓT Q hQK hunit hsepQ
    have hQi : InjOn (Set.IccExtend hTlen Q) (Icc 0 ℓ) :=
      lemma41_bcf_intrinsic_geodesic_injOn K hTlen Q hQK hunit
    exact lemma41_outer_family_forcing hd hδ hsmall hT hTconn ρ hρ E a₁ c₃ P hb
      hdiam hTlen hℓ0 hℓT Q hQK hQi hsepQ

/-- The annular result in the exact endpoint-based argument order of `lemma32_shortcut`.
Use its separation threshold `b₀ = b / 4`. -/
theorem Lemma41OuterRoutingResult.forcing_shortcut {d : ℕ} {δ : ℝ}
    {hd : 1 ≤ d} {hδ : 0 < δ} {hsmall : δ ≤ 1 / (4 * Real.sqrt d)}
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    {ρ : (configOuter d) × (configOuter d) → ℝ} {hρ : IsCoordinate ρ}
    {E : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞}
    {γ : T.edgeSet → ℝ → configOuter d} {a₁ c₃ : ℝ}
    (R : Lemma41OuterRoutingResult hd hδ hsmall T ρ hρ E γ a₁ c₃)
    {b : ℝ} (hb : 0 < b)
    (hdiam : ∀ v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2),
      ∀ x ∈ lemma41_outerMeshStar ρ hρ v,
      ∀ y ∈ lemma41_outerMeshStar ρ hρ v, dist x y < b / 8)
    {Tlen : ℝ} (hTlen : 0 ≤ Tlen)
    (p q : MetricFunSpace ρ hρ.metric) (_hp : p ∈ R.K) (_hq : q ∈ R.K)
    (hpq : b / 4 ≤ dist p q)
    (Q : Icc (0 : ℝ) Tlen →ᵇ MetricFunSpace ρ hρ.metric)
    (hQK : ∀ t, Q t ∈ R.K)
    (hQ0 : Set.IccExtend hTlen Q 0 = p)
    (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓT : ℓ ≤ Tlen)
    (hQℓ : Q ⟨ℓ, ⟨hℓ0, hℓT⟩⟩ = q)
    (hunit : ∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
      internalEDist R.K (Set.IccExtend hTlen Q s) (Set.IccExtend hTlen Q t) =
        ENNReal.ofReal (t - s)) :
    ∃ e : T.edgeSet, TraversesMarkedArc hℓT Q (R.σ e) ∨
      TraversesMarkedArc hℓT Q (fun r => R.σ e (1 - r)) := by
  have hQseg : ∀ u ∈ Icc (0 : ℝ) ℓ, Set.IccExtend hTlen Q u ∈ R.K := by
    intro u hu
    rw [Set.IccExtend_of_mem hTlen Q ⟨hu.1, hu.2.trans hℓT⟩]
    exact hQK ⟨u, ⟨hu.1, hu.2.trans hℓT⟩⟩
  have hsep : b / 4 ≤ dist (Set.IccExtend hTlen Q 0)
      (Set.IccExtend hTlen Q ℓ) := by
    rw [hQ0, Set.IccExtend_of_mem hTlen Q ⟨hℓ0, hℓT⟩, hQℓ]
    exact hpq
  exact R.forcing hb hdiam hTlen hℓ0 hℓT Q hQseg hunit hsep

/-- Coordinate-pair form: the second length is the partition length of `ζtilde` on `U`.
The proof uses its values along the supplied witnesses and marked subarcs only. -/
theorem lemma41_outer_routing_coordinates {d : ℕ} (hd : 3 ≤ d)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (hTconn : T.Connected)
    (ζ : (configOuter d) × (configOuter d) → ℝ) (hζ : IsCoordinate ζ)
    (hreal : ∀ {O : Set (configOuter d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ζ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ζ hζ.metric x)
            (MetricFunSpace.pt ζ hζ.metric y),
          (∀ r, LQGMetric.metricFunSpaceVal ζ hζ.metric (P r) ∈ O) ∧
          pathLength P ≠ ∞)
    (ζtilde : (configOuter d) × (configOuter d) → ℝ)
    (hζtilde : IsCoordinate ζtilde)
    (γ : T.edgeSet → ℝ → configOuter d)
    (hγc : ∀ e, ContinuousOn (γ e) (Icc 0 1))
    (hγi : ∀ e, InjOn (γ e) (Icc 0 1))
    (hγbox : ∀ e, ∀ r ∈ Icc (0 : ℝ) 1,
      (γ e r).1 ∈ centralBox δ
        (Topology.latticePoint δ (lemma41_meshLeft e).1)
        (Topology.latticePoint δ (lemma41_meshRight e).1))
    (hγlen : ∀ e, curveLength (MetricFunSpace.pt ζ hζ.metric ∘ γ e) 0 1 ≠ ∞)
    {a₁ c₂ c₃ : ℝ} (ha₁ : 0 < a₁) (hc₂₃ : c₂ < c₃)
    (hsep : ∀ e, a₁ ≤ ζ (γ e 0, γ e 1))
    (hγtilde : ∀ e,
      curveLengthWith (fun x y : configOuter d => ENNReal.ofReal (ζtilde (x, y)))
        (γ e) 0 1 ≤ ENNReal.ofReal (c₂ * ζ (γ e 0, γ e 1))) :
    Nonempty (Lemma41OuterRoutingResult (by omega : 1 ≤ d) hδ hsmall
      T ζ hζ (lemma41_outerCoordinateCost ζ hζ ζtilde) γ a₁ c₃) := by
  classical
  letI : Fintype (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    (routingMesh_finite hδ).fintype
  letI : Nontrivial (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    lemma41_routing_mesh_nontrivial (by omega : 1 ≤ d) hδ hsmall
  obtain ⟨e, _⟩ := lemma41_tree_incident hTconn
    (Classical.choice (inferInstance : Nonempty
      (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))))
  have hζpos : 0 < ζ (γ e 0, γ e 1) := lt_of_lt_of_le ha₁ (hsep e)
  have hγne : γ e 0 ≠ γ e 1 := by
    intro heq
    have h := hγi e (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) heq
    norm_num at h
  have htildepos : 0 < ζtilde (γ e 0, γ e 1) := by
    have hnonneg : 0 ≤ ζtilde (γ e 0, γ e 1) := by
      change 0 ≤ dist (MetricFunSpace.pt ζtilde hζtilde.metric (γ e 0))
        (MetricFunSpace.pt ζtilde hζtilde.metric (γ e 1))
      exact dist_nonneg
    have hne : ζtilde (γ e 0, γ e 1) ≠ 0 :=
      fun h => hγne (hζtilde.metric.eq_of_eq_zero _ _ h)
    exact lt_of_le_of_ne hnonneg hne.symm
  have hc₂ : 0 ≤ c₂ := by
    by_contra h
    have hprod : c₂ * ζ (γ e 0, γ e 1) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge h) hζpos
    have hzero : ENNReal.ofReal (c₂ * ζ (γ e 0, γ e 1)) = 0 :=
      ENNReal.ofReal_eq_zero.mpr hprod.le
    have hlow : ENNReal.ofReal (ζtilde (γ e 0, γ e 1)) ≤
        curveLengthWith (fun x y : configOuter d => ENNReal.ofReal (ζtilde (x, y)))
          (γ e) 0 1 := le_curveLengthWith
            (δ := fun x y : configOuter d => ENNReal.ofReal (ζtilde (x, y)))
            (P := γ e) zero_le_one
    have hle := hlow.trans (hγtilde e)
    rw [hzero] at hle
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr htildepos)) hle
  apply lemma41_outer_routing hd hδ hsmall hT hTconn ζ hζ hreal
    (lemma41_outerCoordinateCost ζ hζ ζtilde) γ hγc hγi hγbox hγlen
    ha₁ hc₂ hc₂₃ hsep
  intro e
  rw [lemma41_outerCoordinateCost_length]
  exact hγtilde e

end HigherDimLQGMetric
