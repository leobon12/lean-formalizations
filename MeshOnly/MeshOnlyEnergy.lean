import MeshOnly.MeshOnlyLocalization
import BouRabeeGwynne.Section3HarmonicInput
import BouRabeeGwynne.Section3InternalMass

/-!
# The mesh-only energy estimate

This is the energy part of Lemma 5.1 of the volume-notation draft. It reuses
the proved finite-volume consistency and geometric volume estimates. The
weighted L² estimate additionally needs the new support inequality.
-/

open scoped Classical Topology ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The energy error is at most `9 d Vol(Q) M² mesh²` when Q contains the closed
graph region's cells and Taylor balls. No lower bound on cell volumes occurs. -/
theorem harmonic_error_energy_le_collar (hd : 1 ≤ d)
    (U : Set (Euc d)) [Fintype (T.closedVertices U)]
    (hD : T.V → ℝ) (h : Euc d → ℝ) (hmesh : T.mesh ≠ ∞)
    {M : ℝ} (hM : 0 ≤ M)
    (hsol : T.SolvesDirichlet U (fun v => h (T.pos v)) hD)
    {Q W : Set (Euc d)} (hQfinite : μHE[d] Q ≠ ∞)
    (hQD : Q ⊆ interior T.domain) (hQW : Q ⊆ W)
    (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hcellQ : ∀ v : T.closedVertices U, (T.cell v).carrier ⊆ Q)
    (hballQ : ∀ v : T.closedVertices U,
      Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆ Q)
    (hH : ∀ x ∈ Q, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    (T.finiteNetwork (T.closedVertices U)).energy
      (fun v => hD v - h (T.pos v)) ≤
        (9 * (d : ℝ) * (μHE[d] Q).toReal * M ^ 2) * T.mesh.toReal ^ 2 := by
  have hcellD : ∀ v ∈ T.finiteInterior U, (T.cell v).carrier ⊆ interior T.domain :=
    fun v _ => (hcellQ v).trans hQD
  have hneighbors : ∀ v ∈ T.finiteInterior U, ∀ w,
      T.adj v w → w ∈ T.closedVertices U := by
    intro v hv w hvw
    exact T.neighbor_mem_closedVertices hv hvw
  have he := T.harmonic_error_energy_le_incidentMass hd (T.closedVertices U)
    (T.finiteInterior U) (fun v => hD v) h hmesh hM
    (T.solvesDirichlet_restrict hsol) hcellD hneighbors hW hh
    (fun v => (hballQ v).trans hQW) (fun v x hx => hH x (hballQ v hx))
  have hm := T.incidentMass_le_dim_mul_volume hd (T.closedVertices U)
    (T.finiteInterior U) hQfinite hcellQ
  calc
    _ ≤ (3 * M * T.mesh.toReal) ^ 2 *
        T.incidentMass (T.closedVertices U) (T.finiteInterior U) := he
    _ ≤ (3 * M * T.mesh.toReal) ^ 2 * ((d : ℝ) * (μHE[d] Q).toReal) :=
      mul_le_mul_of_nonneg_left hm (sq_nonneg _)
    _ = _ := by ring

end BouRabeeGwynne.OrthogonalTiling
