import MeshOnly.MeshOnlyLocalization
import BouRabeeGwynne.Section4BallExitLevyProkhorov

/-!
# MR p. 3, path-to-boundary paragraph (small-mesh regime)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace BouRabeeGwynne.MeshRates

/-- MR p. 3 (path-to-boundary paragraph), in the small-mesh regime in which MR uses it: if the
`ε`-neighbourhood of `U` lies in the interior of the tiled set, the closed region `V[U] ∪ ∂V[U]` is finite,
every vertex of `V[U]` is joined to `∂V[U]`, and (7) is uniquely solvable for every boundary datum. -/
theorem mr_p3_pathToBoundary {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    (hU : Bornology.IsBounded U) (hmesh : T.mesh ≠ ∞)
    (hcoll : Metric.cthickening T.mesh.toReal U ⊆ interior T.domain) :
    T.HasFiniteAccessibleRegion U ∧ ∀ g : T.V → ℝ, T.HasUniqueDirichletExtension U g := by
  have hcells : ∀ v : T.V, T.pos v ∈ U → (T.cell v).carrier ⊆ interior T.domain := by
    intro v hv
    have h1 := T.toTilingData.cell_subset_cthickening hv hmesh le_rfl
    rw [Metric.cthickening_closure] at h1
    exact h1.trans hcoll
  have hclU : closure U ⊆ interior T.domain :=
    (closure_minimal (Metric.self_subset_cthickening U) Metric.isClosed_cthickening).trans hcoll
  have hfin : (T.closedVertices U).Finite :=
    T.closedVertices_finite hU (hclU.trans interior_subset)
      fun v hv => (hcells v hv).trans interior_subset
  letI : Fintype (T.closedVertices U) := hfin.fintype
  have ha := T.finiteNetwork_boundaryAccessible_of_cell_interior
    hd (EuclideanSpace.single ⟨0, hd⟩ 1) (by simp) (T.closedVertices U) (T.finiteInterior U)
    (fun v hv w hvw => T.neighbor_mem_closedVertices hv hvw) (fun v hv => hcells v hv)
  refine ⟨⟨hfin, ha⟩, fun g => ?_⟩
  have hsol := T.dirichletSolution_spec U ha g
  exact ⟨T.dirichletSolution U ha g, hsol, fun k hk => T.dirichlet_unique_on_closed ha hk hsol⟩

end BouRabeeGwynne.MeshRates
