import MeshOnly.MeshOnlyLocalization
import BouRabeeGwynne.CoordinateHyperplane
import BouRabeeGwynne.TilingDirichlet
import Mathlib.Analysis.Calculus.MeanValue

/-! Maximum-principle and continuum-oscillation inputs for the uniform spike
argument. All graph accessibility follows from the existing geometric proof. -/

open MeasureTheory
open scoped Classical Topology

namespace BouRabeeGwynne

namespace TilingSequence

theorem eventually_finite_boundaryAccessible {n : ℕ} (G : TilingSequence (n+1))
    (hmesh : G.MeshConverges) {U : Set (Euc (n+1))}
    (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain) :
    ∀ᶠ k in Filter.atTop,
      ∃ hfin : ((G.tiling k).closedVertices U).Finite,
        letI : Fintype ((G.tiling k).closedVertices U) := hfin.fintype
        ((G.tiling k).finiteNetwork ((G.tiling k).closedVertices U)).BoundaryAccessible
          ((G.tiling k).finiteInterior U) := by
  filter_upwards [G.eventually_closedVertices_finite hmesh hU hUD,
    G.eventually_interior_cells_subset_domain hmesh hU hUD] with k hfin hcells
  refine ⟨hfin, ?_⟩
  letI : Fintype ((G.tiling k).closedVertices U) := hfin.fintype
  apply (G.tiling k).finiteNetwork_boundaryAccessible_of_cell_interior
    (by omega : 1 ≤ n+1) (coordinateAxis (0 : Fin (n+1))) (coordinateAxis_ne_zero _)
  · intro v hv w hw
    exact (G.tiling k).neighbor_mem_closedVertices hv hw
  · intro v hv
    simpa only [G.common_domain k] using hcells v hv

end TilingSequence

namespace FiniteConductanceNetwork

theorem abs_le_of_solvesDirichlet {V : Type*} [Fintype V]
    (N : FiniteConductanceNetwork V) (A : Set V) (haccess : N.BoundaryAccessible A)
    {g f : V → ℝ} (hsol : N.SolvesDirichlet A g f) {H : ℝ}
    (hboundary : ∀ v, v ∉ A → |g v| ≤ H) : ∀ v, |f v| ≤ H := by
  have hzero : N.SolvesDirichlet A (0 : V → ℝ) 0 := by
    constructor
    · intro v _
      simp [laplacian]
    · intro v _
      rfl
  have h := N.dirichlet_stability A haccess hsol hzero
    (fun v hv => by simpa only [Pi.zero_apply, sub_zero] using hboundary v hv)
  simpa only [Pi.zero_apply, sub_zero] using h

end FiniteConductanceNetwork

theorem meshOnly_harmonic_oscillation {d : ℕ} {h : Euc d → ℝ}
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    {M : ℝ} (hM : ∀ x ∈ W, ‖fderiv ℝ h x‖ ≤ M)
    {z x y : Euc d} {r : ℝ} (hBW : Metric.ball z r ⊆ W)
    (hx : x ∈ Metric.ball z r) (hy : y ∈ Metric.ball z r) :
    |h y - h x| ≤ M * dist y x := by
  have hdiff : ∀ w ∈ Metric.ball z r, DifferentiableAt ℝ h w := by
    intro w hw
    exact ((hh.1.differentiableOn (by norm_num)) w (hBW hw)).differentiableAt
      (hW.mem_nhds (hBW hw))
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun w hw => hM w (hBW hw)) (convex_ball z r) hx hy
  simpa only [Real.norm_eq_abs, dist_eq_norm] using h

end BouRabeeGwynne
