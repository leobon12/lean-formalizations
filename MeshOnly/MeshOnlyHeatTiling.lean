import MeshOnly.MeshOnlyHeatBound
import MeshOnly.MeshOnlySobolevNash

/-! The local form of Proposition 3.1 used for Theorem 1.1. Geometry is
required only at active vertices: their cells lie inside the covered domain
and all their neighbors are in the finite ambient network. Mesh/collar
localization discharges these conditions for the actual interior region. -/

open MeasureTheory
open scoped BigOperators Classical NNReal ENNReal

namespace BouRabeeGwynne

/-- Dimension-only heat and survival estimates for the actual tiling-volume
clock, localized to a finite ambient network containing the active neighbors. -/
theorem meshOnly_local_heat_and_survival {n : ℕ} (hdim : 2 ≤ n + 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : OrthogonalTiling (n+1))
      (R : Set T.V) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
      (S : Set R), T.mesh ≠ ∞ →
      (∀ v ∈ S, (T.cell v).carrier ⊆ interior T.domain) →
      (∀ v ∈ S, ∀ w : T.V, T.adj v w → w ∈ R) →
      ∀ ε : ℝ, 0 < ε → T.mesh.toReal ≤ ε → ∀ x ∈ S,
        (∀ t : ℝ, 0 < t →
          (T.finiteNetwork R).killedHeatDensity
            (fun v : R => (T.cell v).volume.toReal) S x (2*t) x ≤
              K * (t^(-((n+1 : ℕ) : ℝ)/2) + ε^(n+1)*t^(-((n+1 : ℕ) : ℝ)))) ∧
        (∀ t : ℝ≥0, 0 < (t : ℝ) → ε^2 ≤ (t : ℝ) →
          ((T.finiteNetwork R).poissonizedUniformizedLaw
            (fun v : R => (T.cell v).volume.toReal)
            (fun v => T.meshOnly_cellVolume_toReal_pos v) S x t S).toReal ≤
              K * Real.sqrt (∑ v : R, S.indicator (fun v => (T.cell v).volume.toReal) v) *
                (t : ℝ)^(-((n+1 : ℕ) : ℝ)/4)) := by
  obtain ⟨K, hK, hb⟩ := MeshOnlyHeat.heat_and_survival_bounds_from_defective_nash
    (by omega : 1 ≤ n+1) (MeshOnlySobolev.nashConstant_pos hdim).le
  refine ⟨K, hK, ?_⟩
  intro T R _ _ _ S hmesh hcell hneighbors ε hε hbound x hx
  apply hb (T.finiteNetwork R) (fun v : R => (T.cell v).volume.toReal)
    (fun v => T.meshOnly_cellVolume_toReal_pos v) S ε hε ?_ x hx
  intro f hf
  have hmem {v : R} (hv : f v ≠ 0) : v ∈ S := by
    by_contra hout
    have heq := congrFun hf v
    exact hv (by simpa [hout] using heq.symm)
  exact T.meshOnly_defectiveNash_of_mesh_le hdim R f hmesh
    (fun v hv => hcell v (hmem hv))
    (fun v hv w hw => hneighbors v (hmem hv) w hw) ε hbound

end BouRabeeGwynne
