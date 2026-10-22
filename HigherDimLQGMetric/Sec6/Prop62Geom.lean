import HigherDimLQGMetric.Sec6.Prop62Prob
import HigherDimLQGMetric.Sec6.Cor63

/-!
# [S] Proposition 6.2: deterministic geometry on the compact family

Packet S6b. Source: MA3 Details (a) **D-6.2** (*Construction*: `V₀ = A_{7/4,9/4}`, the collar `> 4a`, mesh and
collector with star diameters `≤ b/16` and (18), central boxes), blueprint Part A §6 (`prop:62`, steps
(1)–(4)) with BW1 erratum E6.6 (the star diameters and (18) hold deterministically on `C(β)`).

With the moduli built into the bound datum `β` (lower moduli and upper moduli on the piece `K_{m₀}`
of the compact exhaustion that contains `Ā_{1,3}`):

* `s6b_collar`: every coordinate of `C(β)` is at least `lower_{m₀}(3/4)` between `Ā_{7/4,9/4}` and
  `∂A_{1,3}` (the collar of MA1 (H1), `4 a` with `a = lower_{m₀}(3/4)/4`);
* `s6b_upper_small`: coordinates of `C(β)` are small between Euclidean-close points of the core;
* `s6b_core_realization`: P2 on the core (local exact geodesic realization below `aP`);
* `s6b_access`: the access paths (18) from the collector closure to a mesh vertex;
* `s6b_box_*`: the open neighbourhoods `B(m_e, δ/40)` of the central boxes of a mesh subgraph
  (inputs of Lemma 6.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter BoundedContinuousFunction unitInterval Metric
open _root_.Topology
open HigherDimLFPP (Rd)
open scoped ENNReal
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ### The collar -/

theorem s6b_mem_core_of_frontier {y : Rd d} (hy : y ∈ frontier (ann (0 : Rd d) 1 3)) :
    y ∈ annCl (0 : Rd d) 1 3 ∧ (‖y‖ = 1 ∨ ‖y‖ = 3) := by
  rcases s6b_frontier_ann_subset 0 1 3 hy with h | h
  · rw [mem_sphere, dist_zero_right] at h
    exact ⟨⟨by rw [sub_zero, h], by rw [sub_zero, h]; norm_num⟩, Or.inl h⟩
  · rw [mem_sphere, dist_zero_right] at h
    exact ⟨⟨by rw [sub_zero, h]; norm_num, by rw [sub_zero, h]⟩, Or.inr h⟩

/-- **The collar on `C(β)`.** -/
theorem s6b_collar {β : ConfigBounds d} {q : ConfigC d} (hq : q ∈ configBoundSet β) {m₀ : ℕ}
    (hm₀ : s6bCore d ⊆ configOuterExhaust d m₀) {x y : configOuter d}
    (hx : (x : Rd d) ∈ annCl (0 : Rd d) (7 / 4) (9 / 4))
    (hy : (y : Rd d) ∈ frontier (ann (0 : Rd d) 1 3)) :
    β.outer.lower m₀ (3 / 4) ≤ q.1 (x, y) := by
  obtain ⟨hyc, hy13⟩ := s6b_mem_core_of_frontier hy
  have hxc : x ∈ s6bCore d := by
    change (x : Rd d) ∈ annCl (0 : Rd d) 1 3
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyc' : y ∈ s6bCore d := hyc
  have hdist : 3 / 4 ≤ dist x y := by
    rw [Subtype.dist_eq, dist_eq_norm]
    have h1 := abs_norm_sub_norm_le (x : Rd d) (y : Rd d)
    have hx1 : 7 / 4 ≤ ‖(x : Rd d)‖ := by simpa only [sub_zero] using hx.1
    have hx2 : ‖(x : Rd d)‖ ≤ 9 / 4 := by simpa only [sub_zero] using hx.2
    rcases hy13 with h | h
    · rw [h] at h1
      have := le_abs_self (‖(x : Rd d)‖ - 1)
      linarith
    · rw [h] at h1
      have := neg_abs_le (‖(x : Rd d)‖ - 3)
      linarith
  exact (β.outer.lower_mono m₀ hdist).trans (s6b_lower_core hq hm₀ hxc hyc').1

/-! ### Small coordinates at small Euclidean distance -/

theorem s6b_upper_small (hd : 2 ≤ d) {c C : ℝ} {β : ConfigBounds d} {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) {m₀ : ℕ}
    (hm₀ : s6bCore d ⊆ configOuterExhaust d m₀) {ηu : ℝ} {x y : configOuter d}
    (hx : x ∈ s6bCore d) (hy : y ∈ s6bCore d) (hxy : dist x y ≤ ηu) :
    q.1 (x, y) ≤ β.outer.modulus m₀ ηu :=
  (s6b_upper hd hq (hm₀ hx) (hm₀ hy)).1.trans (β.outer.modulus_mono m₀ hxy)

/-! ### Local realization on the core -/

/-- **P2 on the core**: below a uniform threshold, two core points are joined by an exact coordinate
geodesic. -/
theorem s6b_core_realization (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d) :
    ∃ aP : ℝ, 0 < aP ∧ ∀ q ∈ configCompactFamily hd c C β, ∀ x ∈ s6bCore d, ∀ y ∈ s6bCore d,
      q.1 (x, y) < aP → ∃ Q : I →ᵇ configOuter d, Q 0 = x ∧ Q 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (q.1 (u, v))) (Set.IccExtend zero_le_one Q) 0 1 =
          ENNReal.ofReal (q.1 (x, y)) := by
  set O : Set (configOuter d) := Subtype.val ⁻¹' ann (0 : Rd d) (3 / 4) 4 with hO_def
  have hOU : ann (0 : Rd d) (3 / 4) 4 ⊆ configOuter d := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hO : IsOpen O := (isOpen_ann _ _ _).preimage continuous_subtype_val
  have hcoreO : s6bCore d ⊆ O := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hOc : IsCompact (closure O) := by
    have hK : IsCompact ((Subtype.val : configOuter d → Rd d) ⁻¹' annCl (0 : Rd d) (3 / 4) 4) :=
      trap_isCompact_preimage_val (s6b_isCompact_annCl _ _) fun x hx =>
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
    refine hK.of_isClosed_subset isClosed_closure ?_
    exact closure_minimal (fun x hx => ann_subset_annCl _ _ _ hx)
      ((isClosed_annCl _ _ _).preimage continuous_subtype_val)
  obtain ⟨η, hη, hsep⟩ := s6b_exists_sep s6bCore_isCompact hO hcoreO
  obtain ⟨a', ha', H⟩ := configCompactFamily_outer_P2 hd c C β hcoreO hO hOc η hη hsep
  refine ⟨a' / 4, by positivity, fun q hq x hx y hy hxy => ?_⟩
  obtain ⟨Q, -, hQ0, hQ1, hQlen⟩ := H q hq x hx y hy hxy
  exact ⟨Q, hQ0, hQ1, hQlen⟩

/-! ### The collector and its access paths -/

theorem s6b_closure_collector_subset {δ : ℝ} (hδ : 0 < δ)
    (hδ' : 3 * Real.sqrt d * δ ≤ 1 / 4) :
    closure (meshCollector d δ) ⊆ annCl (0 : Rd d) (7 / 4) (9 / 4) := by
  intro x hx
  obtain ⟨h1, h2⟩ := closure_meshCollector_subset_annCl hδ.le hx
  exact ⟨by linarith, by linarith⟩

theorem s6b_collector_core {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {x : Rd d} (hx : x ∈ closure (meshCollector d δ)) : x ∈ annCl (0 : Rd d) 1 3 :=
  ann_subset_annCl _ _ _ (closure_meshCollector_subset_ann_one_three hδ hsmall hx)

/-- **Access paths (18).** -/
theorem s6b_access (hd : 2 ≤ d) {c C : ℝ} {β : ConfigBounds d} {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) {m₀ : ℕ}
    (hm₀ : s6bCore d ⊆ configOuterExhaust d m₀) {aP ε₀ ηu : ℝ}
    (hP2 : ∀ q ∈ configCompactFamily hd c C β, ∀ x ∈ s6bCore d, ∀ y ∈ s6bCore d,
      q.1 (x, y) < aP → ∃ Q : I →ᵇ configOuter d, Q 0 = x ∧ Q 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (q.1 (u, v))) (Set.IccExtend zero_le_one Q) 0 1 =
          ENNReal.ofReal (q.1 (x, y)))
    (hηu : β.outer.modulus m₀ ηu < min ε₀ aP)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    (hδη : 4 * Real.sqrt d * δ ≤ ηu) (x : configOuter d)
    (hx : (x : Rd d) ∈ closure (meshCollector d δ)) :
    ∃ P : ℝ → configOuter d, ContinuousOn P (Icc 0 1) ∧ P 0 = x ∧
      (∃ v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2),
        P 1 = lemma41_outerPoint (by omega : 1 ≤ d) hδ hsmall v) ∧
      curveLengthWith (fun u v => ENNReal.ofReal (q.1 (u, v))) P 0 1 ≤ ENNReal.ofReal ε₀ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨m, hm, hdist⟩ := exists_meshVertex_dist_le hδ hx
  set v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) := ⟨m, hm⟩
  set w := lemma41_outerPoint hd1 hδ hsmall v with hw_def
  have hwval : (w : Rd d) = Topology.latticePoint δ m := rfl
  have hxc : x ∈ s6bCore d := s6b_collector_core hδ hsmall hx
  have hwc : w ∈ s6bCore d := by
    change (w : Rd d) ∈ annCl (0 : Rd d) 1 3
    rw [hwval]
    refine s6b_collector_core hδ hsmall (subset_closure ?_)
    exact (vertBall_subset_meshCollector hd1 hδ hm) (by
      simp only [vertBall, Metric.mem_ball, dist_self]
      linarith)
  have hxw : dist x w ≤ ηu := by
    rw [Subtype.dist_eq, hwval]
    exact hdist.trans hδη
  have hsmallq := s6b_upper_small hd hq hm₀ hxc hwc hxw
  have hlt : q.1 (x, w) < aP := hsmallq.trans_lt (hηu.trans_le (min_le_right _ _))
  obtain ⟨Q, hQ0, hQ1, hQlen⟩ := hP2 q hq x hxc w hwc hlt
  refine ⟨Set.IccExtend zero_le_one Q, (continuous_IccExtend_iff.mpr Q.continuous).continuousOn,
    ?_, ⟨v, ?_⟩, ?_⟩
  · rw [Set.IccExtend_of_mem zero_le_one Q ⟨le_rfl, zero_le_one⟩]
    exact hQ0
  · rw [Set.IccExtend_of_mem zero_le_one Q ⟨zero_le_one, le_rfl⟩]
    exact hQ1
  · rw [hQlen]
    exact ENNReal.ofReal_le_ofReal (hsmallq.trans (hηu.le.trans (min_le_left _ _)))

/-! ### The boxes of Lemma 6.1 -/

/-- The open neighbourhood `B(m_e, δ/40)` of the central box of a tree edge. -/
def s6bBoxNbhd {δ : ℝ} {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (e : T.edgeSet) : Set (Rd d) :=
  ball (midpoint ℝ (Topology.latticePoint δ (lemma41_meshLeft e).1)
    (Topology.latticePoint δ (lemma41_meshRight e).1)) (δ / 40)

theorem s6b_box_isCompact {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))} (e : T.edgeSet) :
    IsCompact (s6bBox e) :=
  isCompact_centralBox hδ.le _ _

theorem s6b_box_interior (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))} (e : T.edgeSet) :
    (interior (s6bBox e)).Nonempty :=
  nonempty_interior_centralBox hδ hd _ _

theorem s6b_box_subset_nbhd {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))} (e : T.edgeSet) :
    s6bBox e ⊆ s6bBoxNbhd e := by
  intro x hx
  have h := centralBox_subset_closedBall hδ.le _ _ hx
  rw [mem_closedBall] at h
  rw [s6bBoxNbhd, mem_ball]
  linarith

theorem s6b_box_subset_outer (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2)) (e : T.edgeSet) :
    s6bBox e ⊆ configOuter d :=
  lemma41_outer_box_subset hd hδ hsmall (lemma41_meshLeft e).2 (lemma41_tree_edge_adj hT e)

theorem s6b_boxNbhd_subset (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2)) (e : T.edgeSet) :
    s6bBoxNbhd e ⊆ ann (0 : Rd d) 1 3 := by
  intro x hx
  have htube : x ∈ edgeTube δ (Topology.latticePoint δ (lemma41_meshLeft e).1)
      (Topology.latticePoint δ (lemma41_meshRight e).1) := by
    refine mem_thickening_iff.2 ⟨_, midpoint_mem_segment _ _, ?_⟩
    have := mem_ball.1 hx
    linarith
  have hcoll := edgeTube_subset_meshCollector hd hδ (lemma41_meshLeft e).2
    (lemma41_tree_edge_adj hT e) htube
  exact closure_meshCollector_subset_ann_one_three hδ hsmall (subset_closure hcoll)

theorem s6b_boxNbhd_disjoint {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2)) {e f : T.edgeSet}
    (hef : e ≠ f) : Disjoint (s6bBoxNbhd e) (s6bBoxNbhd f) := by
  refine ball_disjoint_ball ?_
  have h := le_dist_midpoint_latticeSegment hδ (lemma41_tree_edge_adj hT e)
    (lemma41_tree_edge_adj hT f) (lemma41_tree_edges_ne e f hef) (midpoint_mem_segment _ _)
  change δ / 2 ≤ dist (midpoint ℝ (Topology.latticePoint δ (e.1.out.1).1)
    (Topology.latticePoint δ (e.1.out.2).1)) (midpoint ℝ (Topology.latticePoint δ (f.1.out.1).1)
    (Topology.latticePoint δ (f.1.out.2).1)) at h
  unfold lemma41_meshLeft lemma41_meshRight
  linarith

end HigherDimLQGMetric
