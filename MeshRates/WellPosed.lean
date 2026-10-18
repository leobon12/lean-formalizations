import MeshOnly.MeshOnlyLocalization

/-!
# Well-posedness of the Dirichlet problem (7) for small mesh (MR p. 3)

Single-tiling version of `TilingSequence.eventually_uniqueDirichletExtension`
(MeshOnly/MeshOnlyLocalization.lean), with the eventual mesh bound replaced by an explicit
threshold depending only on `U` and `K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace BouRabeeGwynne.MeshRates

/-- For small mesh (threshold depending only on `U` and `K`), the closed region `V[U] ∪ ∂V[U]` is
finite and the Dirichlet problem (7) on `V[U]` is uniquely solvable for every boundary datum. -/
theorem wellPosed_of_mesh_le {d : ℕ} (hd : 1 ≤ d) {U K : Set (Euc d)}
    (hUb : Bornology.IsBounded U) (hK : IsOpen K) (hUK : closure U ⊆ K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ T : OrthogonalTiling d, HasAmbientCollar K T.domain →
      T.mesh ≤ ENNReal.ofReal ε₀ →
        (T.closedVertices U).Finite ∧ ∀ g : T.V → ℝ, T.HasUniqueDirichletExtension U g := by
  obtain ⟨ρ, hρ, hρK⟩ := hUb.isCompact_closure.exists_cthickening_subset_open hK hUK
  refine ⟨ρ, hρ, ?_⟩
  intro T hKD hmesh
  have hfin' : T.mesh ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmesh
  have hle : T.mesh.toReal ≤ ρ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmesh
    rwa [ENNReal.toReal_ofReal hρ.le] at this
  have hKint : K ⊆ interior T.domain := subset_closure.trans hKD
  have hcells : ∀ v : T.V, T.pos v ∈ U → (T.cell v).carrier ⊆ interior T.domain :=
    fun v hv => ((T.toTilingData.cell_subset_cthickening hv hfin' hle).trans hρK).trans hKint
  have hfin : (T.closedVertices U).Finite := by
    apply T.closedVertices_finite hUb ((hUK.trans hKint).trans interior_subset)
    intro v hv
    exact (hcells v hv).trans interior_subset
  letI : Fintype (T.closedVertices U) := hfin.fintype
  have hneighbors : ∀ v ∈ T.finiteInterior U, ∀ w,
      T.adj v w → w ∈ T.closedVertices U := by
    intro v hv w hvw
    exact T.neighbor_mem_closedVertices hv hvw
  have hcellD : ∀ v ∈ T.finiteInterior U,
      (T.cell v).carrier ⊆ interior T.domain := by
    intro v hv
    exact hcells v hv
  have ha := T.finiteNetwork_boundaryAccessible_of_cell_interior
    hd (EuclideanSpace.single ⟨0, hd⟩ 1) (by simp) (T.closedVertices U) (T.finiteInterior U)
    hneighbors hcellD
  refine ⟨hfin, ?_⟩
  intro g
  have hsol := T.dirichletSolution_spec U ha g
  refine ⟨T.dirichletSolution U ha g, hsol, ?_⟩
  intro k hk
  exact T.dirichlet_unique_on_closed ha hk hsol

end BouRabeeGwynne.MeshRates
