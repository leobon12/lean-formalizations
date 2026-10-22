import HigherDimLQGMetric.Routing.Lemma41Edge
import HigherDimLQGMetric.Collapse.Graph

/-!
# The finite graph of one routed edge

The witness arc and its two simple rectifiable connectors form a connected finite rectifiable
graph. This elementary assembly is reused for the finite spanning tree.
-/

set_option autoImplicit false

noncomputable section

open Set Topology LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

theorem lemma41_three_arc_graph {X : Type*} [MetricSpace X]
    (βl γ βr : ℝ → X)
    (hβlc : ContinuousOn βl (Icc 0 1)) (hγc : ContinuousOn γ (Icc 0 1))
    (hβrc : ContinuousOn βr (Icc 0 1))
    (hβli : InjOn βl (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hβri : InjOn βr (Icc 0 1))
    (hβllen : curveLength βl 0 1 ≠ ∞) (hγlen : curveLength γ 0 1 ≠ ∞)
    (hβrlen : curveLength βr 0 1 ≠ ∞)
    {u q : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hβl1 : βl 1 = γ u) (hβr1 : βr 1 = γ q) :
    IsFiniteRectGraph
      ((βl '' Icc (0 : ℝ) 1) ∪ (γ '' Icc (0 : ℝ) 1) ∪
        (βr '' Icc (0 : ℝ) 1)) := by
  let A : Set X := βl '' Icc (0 : ℝ) 1
  let B : Set X := γ '' Icc (0 : ℝ) 1
  let C : Set X := βr '' Icc (0 : ℝ) 1
  have hA : IsConnected A := (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image βl hβlc
  have hB : IsConnected B := (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image γ hγc
  have hC : IsConnected C := (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image βr hβrc
  have hAB : (A ∩ B).Nonempty := by
    refine ⟨γ u, ?_, ⟨u, hu, rfl⟩⟩
    exact ⟨1, by norm_num, hβl1⟩
  have hABC : ((A ∪ B) ∩ C).Nonempty := by
    refine ⟨γ q, Or.inr ⟨q, hq, rfl⟩, ?_⟩
    exact ⟨1, by norm_num, hβr1⟩
  have hconn : IsConnected ((A ∪ B) ∪ C) :=
    IsConnected.union hABC (IsConnected.union hAB hA hB) hC
  let F : Fin 3 → ℝ → X := fun i =>
    if i = 0 then βl else if i = 1 then γ else βr
  refine ⟨3, F, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [F, hβlc, hγc, hβrc]
  · intro i
    fin_cases i <;> simp [F, hβli, hγi, hβri]
  · intro i
    fin_cases i <;> simp [F, hβllen, hγlen, hβrlen]
  · change (A ∪ B) ∪ C = ⋃ i, (F i) '' Icc 0 1
    ext z
    simp [A, B, C, F, Fin.exists_fin_succ, or_assoc]
  · exact hconn

end HigherDimLQGMetric
