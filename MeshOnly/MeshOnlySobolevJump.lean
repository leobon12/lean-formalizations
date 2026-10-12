import MeshOnly.MeshOnlySobolevVolumes
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The finite facet-jump estimate in the mesh-only BV argument. -/

open scoped BigOperators Classical

namespace BouRabeeGwynne.MeshOnlySobolev

/-- Weighted Cauchy--Schwarz for the jumps of the squared function, with
each unoriented contact counted exactly once. -/
theorem squared_jump_bound {V : Type*} [Fintype V]
    (a b s : V → V → ℝ) (u : V → ℝ)
    (ha : ∀ v w, 0 ≤ a v w) (hs : ∀ v w, 0 ≤ s v w)
    (hsymm : ∀ v w, s v w = s w v)
    (hfactor : ∀ v w, b v w ^ 2 = a v w * s v w) :
    ((1 / 2 : ℝ) * ∑ v, ∑ w, b v w * |u w ^ 2 - u v ^ 2|) ^ 2 ≤
      2 * ((1 / 2 : ℝ) * ∑ v, ∑ w, a v w * (u w - u v) ^ 2) *
        (∑ v, ∑ w, s v w * u v ^ 2) := by
  have hpoint (v w : V) : (b v w * |u w ^ 2 - u v ^ 2|) ^ 2 ≤
      (a v w * (u w - u v) ^ 2) * (2 * s v w * (u v ^ 2 + u w ^ 2)) := by
    calc
      _ = (a v w * s v w) * (u w - u v) ^ 2 * (u w + u v) ^ 2 := by
        rw [mul_pow, sq_abs, hfactor]
        ring
      _ ≤ _ := by
        have hp : (u w + u v) ^ 2 ≤ 2 * (u v ^ 2 + u w ^ 2) := by
          nlinarith [sq_nonneg (u w - u v)]
        have hnon : 0 ≤ a v w * s v w * (u w - u v) ^ 2 :=
          mul_nonneg (mul_nonneg (ha v w) (hs v w)) (sq_nonneg _)
        nlinarith only [mul_le_mul_of_nonneg_left hp hnon]
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (V × V))
    (r := fun e => b e.1 e.2 * |u e.2 ^ 2 - u e.1 ^ 2|)
    (f := fun e => a e.1 e.2 * (u e.2 - u e.1) ^ 2)
    (g := fun e => 2 * s e.1 e.2 * (u e.1 ^ 2 + u e.2 ^ 2))
    (fun e _ => mul_nonneg (ha _ _) (sq_nonneg _))
    (fun e _ => mul_nonneg (mul_nonneg (by norm_num) (hs _ _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (fun e _ => hpoint e.1 e.2)
  simp only [Fintype.sum_prod_type] at hCS
  have hswap : (∑ v, ∑ w, s v w * u w ^ 2) = ∑ v, ∑ w, s v w * u v ^ 2 := by
    calc
      _ = ∑ v, ∑ w, s w v * u w ^ 2 := by
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro w _
        rw [hsymm v w]
      _ = _ := sum_transpose_weighted s u
  have hmass : (∑ v, ∑ w, 2 * s v w * (u v ^ 2 + u w ^ 2)) =
      4 * ∑ v, ∑ w, s v w * u v ^ 2 := by
    simp_rw [mul_add, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hswap]
    ring
  rw [hmass] at hCS
  nlinarith only [hCS]

end BouRabeeGwynne.MeshOnlySobolev

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Facet area on genuine graph edges and zero elsewhere. The equivalent
conductance-times-length expression fixes the normalization. -/
noncomputable def meshOnlyFacetArea (v w : T.V) : ℝ :=
  T.conductanceReal v w * ‖T.pos w - T.pos v‖

lemma meshOnlyFacetArea_of_adj {v w : T.V} (hvw : T.adj v w) :
    T.meshOnlyFacetArea v w = (T.facetVolume v w).toReal := by
  rw [meshOnlyFacetArea, T.conductanceReal_of_adj hvw]
  exact div_mul_cancel₀ _ (T.edge_norm_pos hvw).ne'

noncomputable def meshOnlySquareJump (R : Set T.V) [Fintype R] (u : R → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
    T.meshOnlyFacetArea v w * |u w ^ 2 - u v ^ 2|

lemma meshOnlySquareJump_nonneg (R : Set T.V) [Fintype R] (u : R → ℝ) :
    0 ≤ T.meshOnlySquareJump R u := by
  unfold meshOnlySquareJump meshOnlyFacetArea
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro v _
  apply Finset.sum_nonneg
  intro w _
  exact mul_nonneg (mul_nonneg (T.conductanceReal_nonneg v w) (norm_nonneg _))
    (abs_nonneg _)

/-- The actual facet jump is bounded by the actual finite-network energy
and the actual primal-cell mass, with no shape regularity hypothesis. -/
theorem meshOnly_squareJump_sq_le (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (u : R → ℝ) (hmesh : T.mesh ≠ ⊤) :
    T.meshOnlySquareJump R u ^ 2 ≤
      (T.finiteNetwork R).energy u *
        (6 * (d : ℝ) * (∑ v : R, (T.cell v).volume.toReal * u v ^ 2) +
          16 * T.mesh.toReal ^ 2 * (T.finiteNetwork R).energy u) := by
  let s : R → R → ℝ := fun v w =>
    (d : ℝ) * (T.meshOnlyPyramidMass v w + T.meshOnlyPyramidMass w v)
  have hbase := MeshOnlySobolev.squared_jump_bound
    (fun v w : R => T.conductanceReal v w)
    (fun v w : R => T.meshOnlyFacetArea v w) s u
    (fun v w => T.conductanceReal_nonneg v w)
    (fun v w => mul_nonneg (Nat.cast_nonneg d)
      (add_nonneg (T.meshOnlyPyramidMass_nonneg v w) (T.meshOnlyPyramidMass_nonneg w v)))
    (fun v w => by dsimp [s]; rw [add_comm])
    (fun v w => by
      dsimp [s, meshOnlyFacetArea]
      rw [← T.conductance_mul_edge_sq_eq_pyramidMass hd]
      ring)
  have hm : (∑ v : R, ∑ w : R, s v w * u v ^ 2) =
      (d : ℝ) * T.meshOnlyDualL2Sq R u := by
    simp only [s, meshOnlyDualL2Sq, Finset.mul_sum, mul_assoc]
  rw [hm] at hbase
  change T.meshOnlySquareJump R u ^ 2 ≤
    2 * (T.finiteNetwork R).energy u * ((d : ℝ) * T.meshOnlyDualL2Sq R u) at hbase
  have hvol := T.meshOnly_dualL2_le_tileL2_add_energy hd R u hmesh
  have henergy := (T.finiteNetwork R).energy_nonneg u
  nlinarith only [hbase,
    mul_le_mul_of_nonneg_left hvol (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) henergy)]

end BouRabeeGwynne.OrthogonalTiling
