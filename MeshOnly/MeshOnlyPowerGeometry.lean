import BouRabeeGwynne.DiscretePDE
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Geometry of the local power-weight increments. These increments are derived
from actual orthogonal contacts. Their assembly into one potential on a ball is
a separate exactness problem; no existence of that potential is assumed here. -/

open scoped ENNReal

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The weight increment forced by equality of the two power functions at y. -/
noncomputable def powerGapAt (v w : T.V) (y : Euc d) : ℝ :=
  ‖y - T.pos w‖ ^ 2 - ‖y - T.pos v‖ ^ 2

lemma powerGapAt_expansion (v w : T.V) (y : Euc d) :
    T.powerGapAt v w y = ‖T.pos w‖ ^ 2 - ‖T.pos v‖ ^ 2 -
      2 * inner ℝ (T.pos w - T.pos v) y := by
  simp only [powerGapAt, norm_sub_sq_real, inner_sub_left]
  rw [real_inner_comm y (T.pos w), real_inner_comm y (T.pos v)]
  ring

/-- Orthogonality makes the forced weight increment constant on the whole
contact, including when that contact is only part of a polytope face. -/
theorem powerGapAt_eq_of_mem_facet {v w : T.V} (hvw : T.adj v w)
    {x y : Euc d} (hx : x ∈ T.facet v w) (hy : y ∈ T.facet v w) :
    T.powerGapAt v w x = T.powerGapAt v w y := by
  have horth := T.orthogonal hvw hx hy
  simp only [inner_sub_right] at horth
  rw [T.powerGapAt_expansion, T.powerGapAt_expansion]
  linarith

/-- A genuine contact determines a canonical edge increment. Values away from
adjacency are zero and have no role in the local compatibility equations. -/
noncomputable def powerEdgeGap (v w : T.V) : ℝ := by
  classical
  exact if hvw : T.adj v w then T.powerGapAt v w (Classical.choose hvw.2.1) else 0

theorem powerEdgeGap_eq {v w : T.V} (hvw : T.adj v w)
    {y : Euc d} (hy : y ∈ T.facet v w) :
    T.powerEdgeGap v w = T.powerGapAt v w y := by
  classical
  simp only [powerEdgeGap, hvw, dite_true]
  exact T.powerGapAt_eq_of_mem_facet hvw (Classical.choose_spec hvw.2.1) hy

theorem powerEdgeGap_rev (v w : T.V) :
    T.powerEdgeGap w v = - T.powerEdgeGap v w := by
  classical
  by_cases hvw : T.adj v w
  · obtain ⟨y, hy⟩ := hvw.2.1
    rw [T.powerEdgeGap_eq (T.toTilingData.adj_symm hvw) ⟨hy.2, hy.1⟩,
      T.powerEdgeGap_eq hvw hy]
    simp only [powerGapAt]
    ring
  · have hwv : ¬ T.adj w v := fun h => hvw (T.toTilingData.adj_symm h)
    simp [powerEdgeGap, hvw, hwv]

/-- The basic bound uses only the two mesh-distance bounds, so it remains true
without any lower bound on cell volumes or face areas. -/
theorem abs_powerEdgeGap_le {v w : T.V} (hvw : T.adj v w)
    (hmesh : T.mesh ≠ ∞) :
    |T.powerEdgeGap v w| ≤ 2 * T.mesh.toReal * ‖T.pos w - T.pos v‖ := by
  obtain ⟨y, hy⟩ := hvw.2.1
  have hv : ‖y - T.pos v‖ ≤ T.mesh.toReal := by
    simpa only [dist_eq_norm] using T.toTilingData.dist_pos_le_mesh hy.1 hmesh
  have hw : ‖y - T.pos w‖ ≤ T.mesh.toReal := by
    simpa only [dist_eq_norm] using T.toTilingData.dist_pos_le_mesh hy.2 hmesh
  have hdist : |‖y - T.pos w‖ - ‖y - T.pos v‖| ≤ ‖T.pos w - T.pos v‖ := by
    have h := abs_norm_sub_norm_le (y - T.pos w) (y - T.pos v)
    simpa only [sub_sub_sub_cancel_left, norm_sub_rev] using h
  rw [T.powerEdgeGap_eq hvw hy, powerGapAt]
  calc
    |‖y - T.pos w‖ ^ 2 - ‖y - T.pos v‖ ^ 2| =
        |‖y - T.pos w‖ - ‖y - T.pos v‖| * (‖y - T.pos w‖ + ‖y - T.pos v‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      ring
    _ ≤ ‖T.pos w - T.pos v‖ * (2 * T.mesh.toReal) :=
      mul_le_mul hdist (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring

/-- Once edge increments are integrated to weights, the corrected squared
distance has exactly the linear normal increment used by the clock identity. -/
theorem correctedSquare_increment {v w : T.V} (hvw : T.adj v w)
    (ω : T.V → ℝ) (hω : ω w - ω v = T.powerEdgeGap v w)
    (z : Euc d) {y : Euc d} (hy : y ∈ T.facet v w) :
    (‖T.pos w - z‖ ^ 2 - ω w) - (‖T.pos v - z‖ ^ 2 - ω v) =
      2 * inner ℝ (T.pos w - T.pos v) (y - z) := by
  rw [T.powerEdgeGap_eq hvw hy, T.powerGapAt_expansion] at hω
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right] at hω ⊢
  linarith

/-- Contact increments already satisfy the cocycle relation whenever three
contacts have a common point. Global exactness needs an additional gluing proof. -/
theorem powerEdgeGap_triangle_of_common_point {u v w : T.V}
    (huv : T.adj u v) (hvw : T.adj v w) (hwu : T.adj w u)
    {y : Euc d} (hyu : y ∈ (T.cell u).carrier)
    (hyv : y ∈ (T.cell v).carrier) (hyw : y ∈ (T.cell w).carrier) :
    T.powerEdgeGap u v + T.powerEdgeGap v w + T.powerEdgeGap w u = 0 := by
  rw [T.powerEdgeGap_eq huv ⟨hyu, hyv⟩, T.powerEdgeGap_eq hvw ⟨hyv, hyw⟩,
    T.powerEdgeGap_eq hwu ⟨hyw, hyu⟩]
  simp only [powerGapAt]
  ring

end BouRabeeGwynne.OrthogonalTiling
