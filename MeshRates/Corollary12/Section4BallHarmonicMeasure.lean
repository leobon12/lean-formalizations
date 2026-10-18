import BouRabeeGwynne.Section4BallHarmonicMeasure
import MeshRates.Corollary12.BallDirichlet

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped Classical Topology ENNReal

namespace BouRabeeGwynne.MeshRates

/-- Copy of `BouRabeeGwynne.eventually_spatialHarmonicMeasure_harmonic_error` (Section4BallHarmonicMeasure.lean:71) with `PaperRegularity` replaced by `BallDirichletInput`.
Proved Theorem B(a) gives a uniform bound for the actual exit expectation
of a continuous function harmonic near the closure. Finiteness and access to
the graph boundary are derived from the geometric approximation assumptions. -/
theorem eventually_spatialHarmonicMeasure_harmonic_error_of_ballDirichlet {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (h : Euc d → ℝ)
    (hDomain : IsDomain U) (hUb : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (happrox : N.ApproximationCondition)
    (hD : BallDirichletInput G) (hh : HarmonicNearClosure h U) (hcont : Continuous h)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in Filter.atTop, ∃ hfin : ((G.tiling n).closedVertices U).Finite,
      letI : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
      letI : MeasurableSpace ((G.tiling n).closedVertices U) := ⊤
      ∃ ha : ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices U)).BoundaryAccessible
          ((G.tiling n).finiteInterior U),
        ∀ v : (G.tiling n).closedVertices U, v ∈ (G.tiling n).finiteInterior U →
          |(∫ x, h x ∂(G.tiling n).spatialHarmonicMeasure U ha v) -
              h ((G.tiling n).pos v)| ≤ η := by
  have hB := hD U h hDomain hUb hUD hh
  obtain ⟨e, he, _⟩ := exists_unit_euc hd
  filter_upwards [hB.1, hB.2 η hη,
    N.eventually_interior_cells_subset_domain happrox hUb hUD] with n hfin herror hcells
  let T := G.tiling n
  let R := T.closedVertices U
  let A := T.finiteInterior U
  refine ⟨hfin.1, ?_⟩
  letI : Fintype R := hfin.1.fintype
  letI : MeasurableSpace R := ⊤
  have hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R := by
    intro v hv w hvw
    exact T.neighbor_mem_closedVertices hv hvw
  have hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain := by
    intro v hv
    simpa only [T, G.common_domain n] using hcells v hv
  have ha := T.finiteNetwork_boundaryAccessible_of_cell_interior hd e he R A
    hneighbors hcellD
  refine ⟨ha, ?_⟩
  intro v hv
  rw [T.integral_spatialHarmonicMeasure U ha hcont v]
  exact herror (T.dirichletSolution U ha (fun w => h (T.pos w)))
    (T.dirichletSolution_spec U ha (fun w => h (T.pos w))) v hv

/-- Copy of `BouRabeeGwynne.eventually_spatialHarmonicMeasure_collar_error` (Section4BallHarmonicMeasure.lean:178) with `PaperRegularity` replaced by `BallDirichletInput`.
A continuum boundary-collar approximation transfers the proved harmonic
test estimate to an actual continuous test of the discrete exit measure.
The two-mesh overshoot is derived from the original tiling geometry. -/
theorem eventually_spatialHarmonicMeasure_collar_error_of_ballDirichlet {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (f h : Euc d → ℝ)
    (hDomain : IsDomain U) (hUb : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (happrox : N.ApproximationCondition)
    (hD : BallDirichletInput G) (hh : HarmonicNearClosure h U)
    (hf : Continuous f) (hcont : Continuous h)
    {δ η ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hnear : ∀ x ∈ Metric.cthickening δ (frontier U), |f x - h x| ≤ η) :
    ∀ᶠ n in Filter.atTop, ∃ hfin : ((G.tiling n).closedVertices U).Finite,
      letI : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
      letI : MeasurableSpace ((G.tiling n).closedVertices U) := ⊤
      ∃ ha : ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices U)).BoundaryAccessible
          ((G.tiling n).finiteInterior U),
        ∀ v : (G.tiling n).closedVertices U, v ∈ (G.tiling n).finiteInterior U →
          |(∫ x, f x ∂(G.tiling n).spatialHarmonicMeasure U ha v) -
              h ((G.tiling n).pos v)| ≤ η + ρ := by
  filter_upwards [eventually_spatialHarmonicMeasure_harmonic_error_of_ballDirichlet hd G N U h
    hDomain hUb hUD happrox hD hh hcont hρ,
    N.eventually_mesh_finite_le happrox (half_pos hδ)] with n hn hmesh
  obtain ⟨hfin, hmeasure⟩ := hn
  let T := G.tiling n
  letI : Fintype (T.closedVertices U) := hfin.fintype
  letI : MeasurableSpace (T.closedVertices U) := ⊤
  obtain ⟨ha, herr⟩ := hmeasure
  refine ⟨hfin, ha, ?_⟩
  intro v hv
  have hboundary : ∀ w ∈ T.boundaryVertices U, |f (T.pos w) - h (T.pos w)| ≤ η := by
    intro w hw
    apply hnear
    exact T.boundary_pos_mem_cthickening_frontier hDomain.2.1 hmesh.1
      (by linarith [hmesh.2]) hw
  have herror := herr v hv
  rw [T.integral_spatialHarmonicMeasure U ha hcont v] at herror
  exact (T.abs_integral_spatialHarmonicMeasure_sub_le U ha hf hboundary v (h (T.pos v))).trans
    (add_le_add (le_refl η) herror)

end BouRabeeGwynne.MeshRates
