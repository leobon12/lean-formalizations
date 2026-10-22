import HigherDimLQGMetric.Routing.Lemma41MeshFamily
import HigherDimLQGMetric.Routing.Lemma41FiniteUnion
import HigherDimLQGMetric.Config.Geometry

/-! The annular coordinate carrier used by the actual configurations. -/

set_option autoImplicit false

noncomputable section

open Set Topology HigherDimLFPP LQGMetric.MetricGeometry

namespace HigherDimLQGMetric

def lemma41_outerSet {d : ℕ} (A : Set (Rd d)) : Set (configOuter d) :=
  Subtype.val ⁻¹' A

theorem lemma41_collector_subset_outer {d : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d)) :
    meshCollector d δ ⊆ configOuter d := by
  intro x hx
  have hcl : x ∈ closure (meshCollector d δ) := subset_closure hx
  have hann := closure_meshCollector_subset_ann_one_three hδ hsmall hcl
  dsimp [configOuter, ann] at hann ⊢
  constructor <;> linarith [hann.1, hann.2]

theorem lemma41_outer_region_subset {d : ℕ} (hd : 1 ≤ d) {δ : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {m n : Fin d → ℤ} (hm : m ∈ Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))
    (hadj : (Topology.latticeGraph d).Adj m n) :
    routingRegion δ (Topology.latticePoint δ m) (Topology.latticePoint δ n) ⊆
      configOuter d :=
  (routingRegion_subset_meshCollector hd hδ hm hadj).trans
    (lemma41_collector_subset_outer hδ hsmall)

theorem lemma41_outer_box_subset {d : ℕ} (hd : 1 ≤ d) {δ : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {m n : Fin d → ℤ} (hm : m ∈ Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))
    (hadj : (Topology.latticeGraph d).Adj m n) :
    centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n) ⊆
      configOuter d :=
  (centralBox_subset_meshCollector hd hδ hm hadj).trans
    (lemma41_collector_subset_outer hδ hsmall)

def lemma41_outerPoint {d : ℕ} {δ : ℝ}
    (hd : 1 ≤ d) (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    (v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) : configOuter d :=
  ⟨Topology.latticePoint δ v.1, by
    apply lemma41_collector_subset_outer hδ hsmall
    exact (vertBall_subset_meshCollector hd hδ v.property)
      (by simp [vertBall, Metric.mem_ball]; linarith)⟩

end HigherDimLQGMetric
