import HigherDimLQGMetric.Routing.Lemma41Family
import HigherDimLQGMetric.Routing.Lemma41Separation

/-! Unoriented tree edges, their lattice endpoints, and cross-edge geometry. -/

set_option autoImplicit false

noncomputable section

open Set HigherDimLFPP

namespace HigherDimLQGMetric

theorem lemma41_tree_edge_adj {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)}
    (hT : T ≤ Topology.meshGraph δ S) (e : T.edgeSet) :
    (Topology.latticeGraph d).Adj (e.1.out.1).1 (e.1.out.2).1 := by
  apply latticeGraph_adj_of_le_meshGraph hT
  have h : T.Adj e.1.out.1 e.1.out.2 := by
    apply T.mem_edgeSet.mp
    simpa only [e.1.out_eq] using e.2
  exact h

theorem lemma41_tree_edges_ne {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)}
    (e f : T.edgeSet) (hef : e ≠ f) :
    s((e.1.out.1).1, (e.1.out.2).1) ≠
      s((f.1.out.1).1, (f.1.out.2).1) := by
  apply Routing.sym2_val_ne
  intro h
  apply hef
  apply Subtype.ext
  calc
    e.1 = s(e.1.out.1, e.1.out.2) := e.1.out_eq.symm
    _ = s(f.1.out.1, f.1.out.2) := h
    _ = f.1 := f.1.out_eq

theorem lemma41_routing_mesh_nontrivial {d : ℕ} (hd : 1 ≤ d)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d)) :
    Nontrivial (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) := by
  have : Nontrivial (Rd d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨p, hp⟩ : (Metric.sphere (0 : Rd d) 2).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  have hpNorm : ‖p‖ = 2 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp
  have hneg : -p ∈ Metric.sphere (0 : Rd d) 2 := by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using hp
  let m := Topology.floorCorner δ p
  let n := Topology.floorCorner δ (-p)
  have hm : m ∈ Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) :=
    floorCorner_mem_meshVertices hδ hp
  have hn : n ∈ Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) :=
    floorCorner_mem_meshVertices hδ hneg
  have hdist : dist p (-p) = 4 := by
    calc
      dist p (-p) = ‖p + p‖ := by rw [dist_eq_norm]; congr 1; abel
      _ = ‖(2 : ℝ) • p‖ := by rw [two_smul]
      _ = 4 := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hpNorm]; norm_num
  have hmn : m ≠ n := by
    intro heq
    have hpm := dist_latticePoint_floorCorner_le hδ p
    have hnm := dist_latticePoint_floorCorner_le hδ (-p)
    have htri := dist_triangle p (Topology.latticePoint δ m) (-p)
    have hsmall' := Routing.three_sqrt_mul_le (d := d) hsmall
    dsimp only [m, n] at heq
    rw [← heq] at hnm
    rw [dist_comm] at hnm
    linarith
  exact nontrivial_iff.mpr
    ⟨⟨m, hm⟩, ⟨n, hn⟩, fun h => hmn (congrArg Subtype.val h)⟩

theorem lemma41_tree_incident {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    [Nontrivial (Topology.meshVertices δ S)]
    {T : SimpleGraph (Topology.meshVertices δ S)} (hT : T.Connected)
    (v : Topology.meshVertices δ S) :
    ∃ e : T.edgeSet, v ∈ (e : Sym2 (Topology.meshVertices δ S)) := by
  obtain ⟨w, hw⟩ := hT.preconnected.exists_adj_of_nontrivial v
  exact ⟨⟨s(v, w), T.mem_edgeSet.mpr hw⟩, Sym2.mem_mk_left v w⟩

theorem lemma41_tree_incident_out {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    [Nontrivial (Topology.meshVertices δ S)]
    {T : SimpleGraph (Topology.meshVertices δ S)} (hT : T.Connected)
    (v : Topology.meshVertices δ S) :
    ∃ e : T.edgeSet, v = e.1.out.1 ∨ v = e.1.out.2 := by
  obtain ⟨e, he⟩ := lemma41_tree_incident hT v
  refine ⟨e, ?_⟩
  rw [← e.1.out_eq] at he
  exact Sym2.mem_iff.mp he

end HigherDimLQGMetric
