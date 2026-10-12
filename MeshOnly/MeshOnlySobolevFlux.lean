import BouRabeeGwynne.PolytopeGaussGreen
import BouRabeeGwynne.DiscretePDEAlgebra

/-! Exact finite cellwise integration by parts, with test-support boundary
cutoffs. The region need not be closed under taking graph neighbors. -/

open scoped Classical BigOperators ENNReal MeasureTheory Topology
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

/-- One coordinate of the actual outward contact flux of a scalar test
function, explicitly zero on nonedges. -/
noncomputable def meshOnlyCoordinateContactFlux (i : Fin (n + 1))
    (φ : Euc (n + 1) → ℝ) (v w : T.V) : ℝ :=
  if T.adj v w then
    ∫ x in T.facet v w,
      ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) * φ x ∂μHE[n]
  else 0

lemma meshOnlyCoordinateContactFlux_rev (i : Fin (n + 1))
    (φ : Euc (n + 1) → ℝ) (v w : T.V) :
    T.meshOnlyCoordinateContactFlux i φ w v =
      -T.meshOnlyCoordinateContactFlux i φ v w := by
  by_cases hvw : T.adj v w
  · rw [meshOnlyCoordinateContactFlux, if_pos (T.toTilingData.adj_symm hvw),
      meshOnlyCoordinateContactFlux, if_pos hvw]
    have hfacet : T.facet w v = T.facet v w := by
      change (T.cell w).carrier ∩ (T.cell v).carrier =
        (T.cell v).carrier ∩ (T.cell w).carrier
      exact Set.inter_comm _ _
    rw [hfacet]
    have hcoord : (T.pos v - T.pos w) i = -(T.pos w - T.pos v) i := by
      change T.pos v i - T.pos w i = -(T.pos w i - T.pos v i)
      ring
    rw [norm_sub_rev, hcoord]
    simp only [neg_div, neg_mul, integral_neg]
  · have hwv : ¬ T.adj w v := fun h => hvw (T.toTilingData.adj_symm h)
    simp [meshOnlyCoordinateContactFlux, hvw, hwv]

lemma meshOnlyCoordinateContactFlux_eq_zero (i : Fin (n + 1))
    (φ : Euc (n + 1) → ℝ) (v w : T.V)
    (hzero : ∀ x ∈ T.facet v w, φ x = 0) :
    T.meshOnlyCoordinateContactFlux i φ v w = 0 := by
  unfold meshOnlyCoordinateContactFlux
  split_ifs
  · exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => by rw [hzero x hx, mul_zero]
  · rfl

/-- Restricting the contact flux sum to a finite region is exact whenever the
test function vanishes on every contact crossing its boundary. -/
theorem meshOnly_sum_coordinate_flux_eq_integral
    (i : Fin (n + 1)) (R : Set T.V) [Fintype R] (v : R)
    (hvD : (T.cell v).carrier ⊆ interior T.domain)
    (φ : Euc (n + 1) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcut : ∀ w : T.V, w ∉ R → T.adj v w → ∀ x ∈ T.facet v w, φ x = 0) :
    (∑ w : R, T.meshOnlyCoordinateContactFlux i φ v w) =
      ∫ x in (T.cell v).carrier, (fderiv ℝ φ x) (coordinateAxis i) ∂volume := by
  have hv := T.neighbors_finite v (hvD.trans interior_subset)
  let N := T.neighborFinset v hv
  let K := T.meshOnlyCoordinateContactFlux i φ v
  have hR : (∑ w ∈ R.toFinset, K w) = ∑ w ∈ R.toFinset ∪ N, K w := by
    apply Finset.sum_subset Finset.subset_union_left
    intro w _ hwR
    have hnot : w ∉ R := fun h => hwR (Set.mem_toFinset.mpr h)
    by_cases hvw : T.adj v w
    · exact T.meshOnlyCoordinateContactFlux_eq_zero i φ v w (hcut w hnot hvw)
    · simp [K, meshOnlyCoordinateContactFlux, hvw]
  have hN : (∑ w ∈ N, K w) = ∑ w ∈ R.toFinset ∪ N, K w := by
    apply Finset.sum_subset Finset.subset_union_right
    intro w _ hwN
    have hnot : ¬ T.adj v w := fun h => hwN ((T.mem_neighborFinset hv).mpr h)
    simp [K, meshOnlyCoordinateContactFlux, hnot]
  rw [Finset.sum_set_coe R (f := K), hR, ← hN]
  calc
    _ = ∑ w ∈ T.neighborFinset v hv,
        ∫ x in T.facet v w,
          ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) * φ x ∂μHE[n] := by
      apply Finset.sum_congr rfl
      intro w hw
      exact if_pos ((T.mem_neighborFinset hv).mp hw)
    _ = _ := T.sum_coordinate_contact_integral_eq_integral_fderiv i v hvD hv
      isOpen_univ (Set.subset_univ _) hφ.contDiffOn

/-- Finite cellwise integration by parts pairs both orientations of each
contact. Boundary contacts absent from R are harmless exactly when the test
function vanishes there. This is the scalar jump identity used in mollification. -/
theorem meshOnly_sum_cell_partial_by_parts
    (i : Fin (n + 1)) (R : Set T.V) [Fintype R] (c : R → ℝ)
    (φ : Euc (n + 1) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcell : ∀ v : R, c v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain)
    (hcut : ∀ v : R, c v ≠ 0 → ∀ w : T.V, w ∉ R → T.adj v w →
      ∀ x ∈ T.facet v w, φ x = 0) :
    (∑ v : R, (∫ x in (T.cell v).carrier,
      (fderiv ℝ φ x) (coordinateAxis i) ∂volume) * c v) =
      -(1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
        T.meshOnlyCoordinateContactFlux i φ v w * (c w - c v) := by
  have heq : (∑ v : R, (∫ x in (T.cell v).carrier,
      (fderiv ℝ φ x) (coordinateAxis i) ∂volume) * c v) =
      ∑ v : R, (∑ w : R, T.meshOnlyCoordinateContactFlux i φ v w) * c v := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases hc : c v = 0
    · simp [hc]
    · rw [T.meshOnly_sum_coordinate_flux_eq_integral i R v (hcell v hc) φ hφ (hcut v hc)]
  rw [heq]
  exact discrete_integration_by_parts
    (fun w v : R => T.meshOnlyCoordinateContactFlux i φ v w) c
    (fun w v => T.meshOnlyCoordinateContactFlux_rev i φ w v)

end BouRabeeGwynne.OrthogonalTiling
