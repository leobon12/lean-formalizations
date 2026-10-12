import MeshOnly.MeshOnlyPowerGeometry
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Actual mollifications of the finite local displacement field. Setting the
field to zero on cell boundaries gives a pointwise bound, while preserving its
almost-everywhere values on the tiling. -/

open scoped Classical BigOperators Convolution Topology ENNReal
open MeasureTheory ContinuousLinearMap

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

noncomputable def meshOnlyDisplacementField (R : Set T.V) [Fintype R] (x : Euc d) : Euc d :=
  ∑ v : R, (interior (T.cell v).carrier).indicator (fun y => (2 : ℝ) • (y - T.pos v)) x

lemma meshOnlyDisplacementField_eq_of_mem_interior (R : Set T.V) [Fintype R]
    (v : R) {x : Euc d} (hx : x ∈ interior (T.cell v).carrier) :
    T.meshOnlyDisplacementField R x = (2 : ℝ) • (x - T.pos v) := by
  unfold meshOnlyDisplacementField
  rw [Finset.sum_eq_single v]
  · exact Set.indicator_of_mem hx _
  · intro w _ hw
    apply Set.indicator_of_notMem
    intro hxw
    exact Set.disjoint_left.mp
      (T.interiors_pairwise_disjoint (fun h => hw (Subtype.ext h))) hxw hx
  · simp

lemma meshOnlyDisplacementField_locallyIntegrable (R : Set T.V) [Fintype R] :
    LocallyIntegrable (T.meshOnlyDisplacementField R) volume := by
  apply locallyIntegrable_finsetSum
  intro v _
  have hc : Continuous (fun y : Euc d => (2 : ℝ) • (y - T.pos v)) := by fun_prop
  exact hc.locallyIntegrable.indicator isOpen_interior.measurableSet

/-- The bound is valid everywhere, including at multiply incident boundaries,
and uses neither minimum cell volume nor lower bounds on face sizes. -/
lemma meshOnlyDisplacementField_norm_le (R : Set T.V) [Fintype R]
    (hmesh : T.mesh ≠ ∞) (x : Euc d) :
    ‖T.meshOnlyDisplacementField R x‖ ≤ 2 * T.mesh.toReal := by
  by_cases hex : ∃ v : R, x ∈ interior (T.cell v).carrier
  · obtain ⟨v, hv⟩ := hex
    rw [T.meshOnlyDisplacementField_eq_of_mem_interior R v hv, norm_smul, Real.norm_ofNat]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [dist_eq_norm] using
      T.toTilingData.dist_pos_le_mesh (interior_subset hv) hmesh
  · have hz : T.meshOnlyDisplacementField R x = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      exact Set.indicator_of_notMem (fun hv => hex ⟨v, hv⟩) _
    rw [hz, norm_zero]
    positivity

noncomputable def meshOnlyMollifiedDisplacement (R : Set T.V) [Fintype R]
    (φ : ContDiffBump (0 : Euc d)) : Euc d → Euc d :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] T.meshOnlyDisplacementField R

theorem meshOnlyMollifiedDisplacement_contDiff (R : Set T.V) [Fintype R]
    (φ : ContDiffBump (0 : Euc d)) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (T.meshOnlyMollifiedDisplacement R φ) := by
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed (T.meshOnlyDisplacementField_locallyIntegrable R)

/-- The genuine smooth convolutions retain the exact 2-mesh bound. -/
theorem meshOnlyMollifiedDisplacement_norm_le (R : Set T.V) [Fintype R]
    (φ : ContDiffBump (0 : Euc d)) (hmesh : T.mesh ≠ ∞) (x : Euc d) :
    ‖T.meshOnlyMollifiedDisplacement R φ x‖ ≤ 2 * T.mesh.toReal := by
  have h := dist_convolution_le (by positivity : 0 ≤ 2 * T.mesh.toReal)
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed
    (T.meshOnlyDisplacementField_locallyIntegrable R).aestronglyMeasurable
    (fun y (_ : y ∈ Metric.ball x φ.rOut) =>
      show dist (T.meshOnlyDisplacementField R y) 0 ≤ 2 * T.mesh.toReal by
        simpa only [dist_zero_right] using T.meshOnlyDisplacementField_norm_le R hmesh y)
  simpa only [dist_zero_right, meshOnlyMollifiedDisplacement] using h

/-- On a cell interior, the mollified field is uniformly close to the actual
affine displacement field, with error at most twice the mollifier radius. -/
theorem meshOnlyMollifiedDisplacement_dist_le_of_ball_subset
    (R : Set T.V) [Fintype R] (v : R) (φ : ContDiffBump (0 : Euc d))
    (x : Euc d) (hball : Metric.ball x φ.rOut ⊆ interior (T.cell v).carrier) :
    dist (T.meshOnlyMollifiedDisplacement R φ x) ((2 : ℝ) • (x - T.pos v)) ≤
      2 * φ.rOut := by
  have hx := hball (Metric.mem_ball_self φ.rOut_pos)
  have h := φ.dist_normed_convolution_le
    (T.meshOnlyDisplacementField_locallyIntegrable R).aestronglyMeasurable
    (fun y (hy : y ∈ Metric.ball x φ.rOut) => show
      dist (T.meshOnlyDisplacementField R y) (T.meshOnlyDisplacementField R x) ≤
        2 * φ.rOut from by
      rw [T.meshOnlyDisplacementField_eq_of_mem_interior R v (hball hy),
        T.meshOnlyDisplacementField_eq_of_mem_interior R v hx,
        dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_ofNat]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [dist_eq_norm] using (Metric.mem_ball.mp hy).le)
  simpa only [meshOnlyMollifiedDisplacement,
    T.meshOnlyDisplacementField_eq_of_mem_interior R v hx] using h

end BouRabeeGwynne.OrthogonalTiling
