import BouRabeeGwynne.Section3WellPosed
import BouRabeeGwynne.Section3CompactCollar

/-!
# Localization from the mesh hypothesis alone

These lemmas use only convergence of the actual extended-real mesh. In
particular, no nearest-vertex choices or alternatives I, II, III are required.
-/

open scoped Topology ENNReal

namespace BouRabeeGwynne.TilingSequence

variable {d : ℕ} (G : TilingSequence d)

/-- The sole approximation hypothesis in the mesh-only draft's Theorem 1.1.
Extended-real convergence also forces eventual finiteness of the mesh. -/
def MeshConverges : Prop :=
  Filter.Tendsto (fun n => (G.tiling n).mesh) Filter.atTop (nhds 0)

theorem eventually_mesh_finite_le (h : G.MeshConverges) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, (G.tiling n).mesh ≠ ∞ ∧ (G.tiling n).mesh.toReal ≤ δ := by
  have hsmall := h.eventually_lt_const (ENNReal.ofReal_pos.mpr hδ)
  filter_upwards [hsmall] with n hn
  refine ⟨(lt_trans hn ENNReal.ofReal_lt_top).ne, ?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn.le
  simpa only [ENNReal.toReal_ofReal hδ.le] using hr

theorem eventually_interior_cells_subset_domain (h : G.MeshConverges)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain) :
    ∀ᶠ n in Filter.atTop, ∀ v : (G.tiling n).V, (G.tiling n).pos v ∈ U →
      ((G.tiling n).cell v).carrier ⊆ interior G.domain := by
  obtain ⟨δ, hδ, hδD⟩ :=
    hU.isCompact_closure.exists_cthickening_subset_open isOpen_interior hUD
  filter_upwards [G.eventually_mesh_finite_le h hδ] with n hn v hv
  exact ((G.tiling n).toTilingData.cell_subset_cthickening hv hn.1 hn.2).trans hδD

theorem eventually_closedVertices_finite (h : G.MeshConverges)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain) :
    ∀ᶠ n in Filter.atTop, ((G.tiling n).closedVertices U).Finite := by
  filter_upwards [G.eventually_interior_cells_subset_domain h hU hUD] with n hn
  apply (G.tiling n).closedVertices_finite hU
  · simpa only [G.common_domain n] using hUD.closure_subset
  · intro v hv
    simpa only [G.common_domain n] using (hn v hv).trans interior_subset

theorem eventually_closedRegion_in_compact_collar (h : G.MeshConverges)
    {U Q : Set (Euc d)} {ρ : ℝ} (hρ : 0 < ρ)
    (hQ : Metric.cthickening ρ (closure U) ⊆ Q) :
    ∀ᶠ n in Filter.atTop, (G.tiling n).mesh ≠ ∞ ∧
      ∀ v ∈ (G.tiling n).closedVertices U,
        ((G.tiling n).cell v).carrier ⊆ Q ∧
        Metric.closedBall ((G.tiling n).pos v) (2 * (G.tiling n).mesh.toReal) ⊆ Q := by
  filter_upwards [G.eventually_mesh_finite_le h (div_pos hρ (by norm_num : (0 : ℝ) < 4))]
    with n hn
  refine ⟨hn.1, ?_⟩
  intro v hv
  have hball : Metric.closedBall ((G.tiling n).pos v)
      (2 * (G.tiling n).mesh.toReal) ⊆ Q :=
    ((G.tiling n).closedVertex_ball_subset_cthickening hn.1 hv).trans
      ((Metric.cthickening_mono (by linarith : 4 * (G.tiling n).mesh.toReal ≤ ρ)
        (closure U)).trans hQ)
  refine ⟨?_, hball⟩
  intro x hx
  apply hball
  apply Metric.mem_closedBall.mpr
  have hdist := (G.tiling n).toTilingData.dist_pos_le_mesh hx hn.1
  have hε : 0 ≤ (G.tiling n).mesh.toReal := ENNReal.toReal_nonneg
  linarith

/-- All boundary data have a unique solution on the eventual finite graph
region. The index is independent of those data. -/
theorem eventually_uniqueDirichletExtension (hd : 1 ≤ d) (e : Euc d) (he : e ≠ 0)
    (h : G.MeshConverges) {U : Set (Euc d)}
    (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain) :
    ∀ᶠ n in Filter.atTop, ((G.tiling n).closedVertices U).Finite ∧
      ∀ g : (G.tiling n).V → ℝ, (G.tiling n).HasUniqueDirichletExtension U g := by
  filter_upwards [G.eventually_closedVertices_finite h hU hUD,
    G.eventually_interior_cells_subset_domain h hU hUD] with n hfin hcells
  letI : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
  have hneighbors : ∀ v ∈ (G.tiling n).finiteInterior U, ∀ w,
      (G.tiling n).adj v w → w ∈ (G.tiling n).closedVertices U := by
    intro v hv w hvw
    exact (G.tiling n).neighbor_mem_closedVertices hv hvw
  have hcellD : ∀ v ∈ (G.tiling n).finiteInterior U,
      ((G.tiling n).cell v).carrier ⊆ interior (G.tiling n).domain := by
    intro v hv
    simpa only [G.common_domain n] using hcells v hv
  have ha := (G.tiling n).finiteNetwork_boundaryAccessible_of_cell_interior
    hd e he ((G.tiling n).closedVertices U) ((G.tiling n).finiteInterior U)
    hneighbors hcellD
  refine ⟨hfin, ?_⟩
  intro g
  let hD := (G.tiling n).dirichletSolution U ha g
  have hsol := (G.tiling n).dirichletSolution_spec U ha g
  refine ⟨hD, hsol, ?_⟩
  intro k hk
  exact (G.tiling n).dirichlet_unique_on_closed ha hk hsol

end BouRabeeGwynne.TilingSequence
