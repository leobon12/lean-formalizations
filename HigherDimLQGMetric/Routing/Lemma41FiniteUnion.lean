import HigherDimLQGMetric.Routing.Lemma41Star
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Finite unions of finite rectifiable graphs

This flattens the finite families of simple arcs from each routed edge into the graph
representation used by S1c.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set LQGMetric.MetricGeometry

namespace HigherDimLQGMetric

theorem lemma41_finite_union_graph {X E : Type*} [MetricSpace X] [Fintype E]
    (K : E → Set X) (hK : ∀ e, IsFiniteRectGraph (K e))
    (hconn : IsConnected (⋃ e, K e)) :
    IsFiniteRectGraph (⋃ e, K e) := by
  classical
  choose m γ hc hi hl hEq _ using hK
  let J := Σ e : E, Fin (m e)
  let equiv : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let F : Fin (Fintype.card J) → ℝ → X := fun i =>
    γ (equiv.symm i).1 (equiv.symm i).2
  refine ⟨Fintype.card J, F, ?_, ?_, ?_, ?_, hconn⟩
  · intro i
    exact hc (equiv.symm i).1 (equiv.symm i).2
  · intro i
    exact hi (equiv.symm i).1 (equiv.symm i).2
  · intro i
    exact hl (equiv.symm i).1 (equiv.symm i).2
  · ext z
    constructor
    · intro hz
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
      rw [hEq e] at he
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp he
      refine Set.mem_iUnion.mpr ⟨equiv ⟨e, j⟩, ?_⟩
      change z ∈ (γ (equiv.symm (equiv ⟨e, j⟩)).1
        (equiv.symm (equiv ⟨e, j⟩)).2) '' Icc 0 1
      rw [equiv.symm_apply_apply]
      exact hj
    · intro hz
      obtain ⟨i, hi'⟩ := Set.mem_iUnion.mp hz
      let j : J := equiv.symm i
      refine Set.mem_iUnion.mpr ⟨j.1, ?_⟩
      rw [hEq j.1]
      exact Set.mem_iUnion.mpr ⟨j.2, hi'⟩

/-- A connected graph of connected sets with intersecting adjacent sets has connected union. -/
theorem lemma41_connected_union_of_graph {X V : Type*} [TopologicalSpace X]
    (G : SimpleGraph V) (hG : G.Connected) (C : V → Set X)
    (hC : ∀ v, IsConnected (C v))
    (hAdj : ∀ v w, G.Adj v w → (C v ∩ C w).Nonempty) :
    IsConnected (⋃ v, C v) := by
  letI : Nonempty V := hG.nonempty
  apply IsConnected.iUnion_of_reflTransGen hC
  intro v w
  exact Relation.ReflTransGen.mono (fun a b hab => hAdj a b hab) v w
    ((G.reachable_iff_reflTransGen v w).mp (hG v w))

/-- A connected line graph and edge pieces containing their endpoint vertices give a connected
geometric union. -/
theorem lemma41_connected_edge_union {X V : Type*} [TopologicalSpace X]
    (G : SimpleGraph V) (hG : G.lineGraph.Connected)
    (p : V → X) (K : G.edgeSet → Set X)
    (hK : ∀ e, IsConnected (K e))
    (hp : ∀ (e : G.edgeSet) (v : V), v ∈ (e : Sym2 V) → p v ∈ K e) :
    IsConnected (⋃ e, K e) := by
  apply lemma41_connected_union_of_graph G.lineGraph hG K hK
  intro e f hef
  obtain ⟨_, v, hve, hvf⟩ := G.lineGraph_adj_iff_exists.mp hef
  exact ⟨p v, hp e v hve, hp f v hvf⟩

/-- Connectedness of an edge graph from the original connected vertex graph. The incidence
assumption excludes isolated vertices, including the one-vertex graph. -/
theorem lemma41_connected_edge_union_of_vertices {X V : Type*}
    [MetricSpace X] [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (hincident : ∀ v, ∃ e : G.edgeSet, v ∈ (e : Sym2 V))
    (p : V → X) (K : G.edgeSet → Set X)
    (hK : ∀ e, IsFiniteRectGraph (K e))
    (hp : ∀ (e : G.edgeSet) (v : V), v ∈ (e : Sym2 V) → p v ∈ K e) :
    IsConnected (⋃ e, K e) := by
  classical
  let A : V → Set X := fun v => {p v} ∪ ⋃ e : G.edgeSet,
    if v ∈ (e : Sym2 V) then K e else {p v}
  have hA : ∀ v, IsConnected (A v) := by
    intro v
    let D : G.edgeSet → Set X := fun e =>
      if v ∈ (e : Sym2 V) then K e else {p v}
    have hDc : ∀ e, IsCompact (D e) := by
      intro e
      by_cases he : v ∈ (e : Sym2 V)
      · simpa only [D, ite_eq_left he] using (hK e).isCompact
      · simp [D, he]
    have hDn : ∀ e, IsConnected (D e) := by
      intro e
      by_cases he : v ∈ (e : Sym2 V)
      · obtain ⟨_, _, _, _, _, _, hconn⟩ := hK e
        simpa only [D, ite_eq_left he] using hconn
      · simpa [D, he] using (isConnected_singleton : IsConnected ({p v} : Set X))
    have hDp : ∀ e, p v ∈ D e := by
      intro e
      by_cases he : v ∈ (e : Sym2 V)
      · simpa only [D, ite_eq_left he] using hp e v he
      · simp [D, he]
    exact (lemma41_star_union (p v) D hDc hDn hDp).2
  have hAdj : ∀ v w, G.Adj v w → (A v ∩ A w).Nonempty := by
    intro v w hvw
    let e : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.mpr hvw⟩
    have hve : v ∈ (e : Sym2 V) := Sym2.mem_mk_left v w
    have hwe : w ∈ (e : Sym2 V) := Sym2.mem_mk_right v w
    refine ⟨p v, Or.inr (Set.mem_iUnion_of_mem e ?_), Or.inr (Set.mem_iUnion_of_mem e ?_)⟩
    · simpa only [ite_eq_left hve] using hp e v hve
    · simpa only [ite_eq_left hwe] using hp e v hve
  have hconn : IsConnected (⋃ v, A v) := lemma41_connected_union_of_graph G hG A hA hAdj
  have heq : (⋃ v, A v) = ⋃ e, K e := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hx
      rcases hv with hv | hv
      · obtain ⟨e, he⟩ := hincident v
        exact Set.mem_iUnion_of_mem e (hv ▸ hp e v he)
      · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
        by_cases hve : v ∈ (e : Sym2 V)
        · exact Set.mem_iUnion_of_mem e (by simpa only [ite_eq_left hve] using he)
        · obtain ⟨f, hf⟩ := hincident v
          have hxv : x = p v := by simpa [hve] using he
          exact Set.mem_iUnion_of_mem f (hxv ▸ hp f v hf)
    · intro hx
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
      let v : V := (e : Sym2 V).out.1
      have hve : v ∈ (e : Sym2 V) := Sym2.out_fst_mem _
      exact Set.mem_iUnion_of_mem v (Or.inr
        (Set.mem_iUnion_of_mem e (by simpa only [ite_eq_left hve] using he)))
  rw [heq] at hconn
  exact hconn

end HigherDimLQGMetric
