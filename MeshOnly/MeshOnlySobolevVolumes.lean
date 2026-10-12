import MeshOnly.MeshOnlySobolevAlgebra
import BouRabeeGwynne.DualVolume
import BouRabeeGwynne.DualVolumeSums
import BouRabeeGwynne.TilingNetwork

/-! Actual pyramid-volume comparison for the mesh-only Sobolev argument. -/

open scoped BigOperators Classical ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The actual volume of the half-dual pyramid based in the first cell,
extended by zero off graph edges. -/
noncomputable def meshOnlyPyramidMass (v w : T.V) : ℝ :=
  if T.adj v w then (μHE[d] (T.toTilingData.cellPyramid v w)).toReal else 0

lemma meshOnlyPyramidMass_nonneg (v w : T.V) : 0 ≤ T.meshOnlyPyramidMass v w := by
  unfold meshOnlyPyramidMass
  split_ifs <;> positivity

lemma meshOnly_pyramid_measure_ne_top (v w : T.V) :
    μHE[d] (T.toTilingData.cellPyramid v w) ≠ ∞ := by
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact (T.toTilingData.cellPyramid_compact v w).measure_lt_top.ne

/-- A finite selection of outward contact pyramids has total volume at most
its primal cell. Completeness of the neighbor selection is not needed here. -/
theorem sum_meshOnlyPyramidMass_le_volume (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (v : T.V) :
    (∑ w : R, T.meshOnlyPyramidMass v w) ≤ (T.cell v).volume.toReal := by
  let F : Finset R := Finset.univ.filter (fun w => T.adj v w)
  have hfin : μHE[d] (T.cell v).carrier ≠ ∞ := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact (T.cell v).compact.measure_lt_top.ne
  have hsum : (∑ w ∈ F, μHE[d] (T.toTilingData.cellPyramid v w)) ≤
      μHE[d] (T.cell v).carrier := by
    rw [← measure_biUnion_finset₀]
    · exact measure_mono (Set.iUnion₂_subset fun w _ =>
        T.toTilingData.cellPyramid_subset_cell v w)
    · intro w hw z hz hwz
      exact T.toTilingData.cellPyramid_aedisjoint hd
        (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hz).2
        (fun h => hwz (Subtype.ext (congrArg Prod.snd h)))
    · intro w _
      exact (T.toTilingData.cellPyramid_compact v w).measurableSet.nullMeasurableSet
  have hreal := ENNReal.toReal_mono hfin hsum
  rw [ENNReal.toReal_sum (fun (w : R) _ => T.meshOnly_pyramid_measure_ne_top v w)] at hreal
  simpa only [meshOnlyPyramidMass, F, Finset.sum_filter, ConvexPolytope.volume] using hreal

lemma meshOnlyPyramidMass_add_reverse (hd : 1 ≤ d) {v w : T.V}
    (hvw : T.adj v w) :
    T.meshOnlyPyramidMass v w + T.meshOnlyPyramidMass w v =
      (T.toTilingData.dualVolume v w).toReal := by
  rw [meshOnlyPyramidMass, if_pos hvw, meshOnlyPyramidMass,
    if_pos (T.toTilingData.adj_symm hvw), T.toTilingData.dualVolume_eq_pyramid_add hd hvw.1,
    ENNReal.toReal_add (T.meshOnly_pyramid_measure_ne_top v w)
      (T.meshOnly_pyramid_measure_ne_top w v)]

/-- Squared edge length converts conductance to the sum of its two actual
pyramid volumes. This preserves the dimension factor exactly. -/
lemma conductance_mul_edge_sq_eq_pyramidMass (hd : 1 ≤ d) (v w : T.V) :
    T.conductanceReal v w * ‖T.pos w - T.pos v‖ ^ 2 =
      (d : ℝ) * (T.meshOnlyPyramidMass v w + T.meshOnlyPyramidMass w v) := by
  by_cases hvw : T.adj v w
  · rw [T.meshOnlyPyramidMass_add_reverse hd hvw,
      ← T.edgeLength_mul_facetVolume_eq_dim_mul_dualVolume hd hvw,
      T.conductanceReal_of_adj hvw]
    have hn := (T.edge_norm_pos hvw).ne'
    field_simp
  · have hwv : ¬ T.adj w v := fun h => hvw (T.toTilingData.adj_symm h)
    simp [conductanceReal, meshOnlyPyramidMass, hvw, hwv]

/-- The geometric vertex-dual mass, restricted to a finite ambient vertex
region. When the function has all support neighbors in this region, this is
the full vertex-dual weighted L² mass. -/
noncomputable def meshOnlyDualL2Sq (R : Set T.V) [Fintype R] (u : R → ℝ) : ℝ :=
  ∑ v : R, ∑ w : R,
    (T.meshOnlyPyramidMass v w + T.meshOnlyPyramidMass w v) * u v ^ 2

/-- Lemma 2.1 in exact tile-volume normalization, for the actual finite graph.
The proof uses genuine disjoint pyramid volumes and the actual mesh bound. -/
theorem meshOnly_dualL2_le_tileL2_add_energy (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (u : R → ℝ) (hmesh : T.mesh ≠ ∞) :
    (d : ℝ) * T.meshOnlyDualL2Sq R u ≤
      3 * (d : ℝ) * (∑ v : R, (T.cell v).volume.toReal * u v ^ 2) +
        8 * T.mesh.toReal ^ 2 * (T.finiteNetwork R).energy u := by
  have hbase := MeshOnlySobolev.dual_mass_le_primal_and_jumps
    (fun v w : R => T.meshOnlyPyramidMass v w)
    (fun v : R => (T.cell v).volume.toReal) u
    (fun v w => T.meshOnlyPyramidMass_nonneg v w)
    (fun v _ => T.sum_meshOnlyPyramidMass_le_volume hd R v)
  have hmul := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hjump : (d : ℝ) * (∑ v : R, ∑ w : R,
      (T.meshOnlyPyramidMass v w + T.meshOnlyPyramidMass w v) * (u w - u v) ^ 2) ≤
      8 * T.mesh.toReal ^ 2 * (T.finiteNetwork R).energy u := by
    calc
      _ = ∑ v : R, ∑ w : R,
          T.conductanceReal v w * ‖T.pos w - T.pos v‖ ^ 2 * (u w - u v) ^ 2 := by
        simp_rw [Finset.mul_sum, ← mul_assoc, T.conductance_mul_edge_sq_eq_pyramidMass hd]
      _ ≤ ∑ v : R, ∑ w : R,
          T.conductanceReal v w * (4 * T.mesh.toReal ^ 2) * (u w - u v) ^ 2 := by
        apply Finset.sum_le_sum
        intro v _
        apply Finset.sum_le_sum
        intro w _
        by_cases hvw : T.adj v w
        · have hlen := T.toTilingData.edge_dist_le_two_mesh hvw hmesh
          rw [dist_eq_norm, norm_sub_rev] at hlen
          have hs : ‖T.pos w - T.pos v‖ ^ 2 ≤ 4 * T.mesh.toReal ^ 2 := by
            nlinarith only [mul_self_le_mul_self (norm_nonneg _) hlen]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hs (T.conductanceReal_nonneg v w)) (sq_nonneg _)
        · simp [conductanceReal, hvw]
      _ = _ := by
        unfold FiniteConductanceNetwork.energy finiteNetwork
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro w _
        ring
  unfold meshOnlyDualL2Sq
  nlinarith only [hmul, hjump]

end BouRabeeGwynne.OrthogonalTiling
