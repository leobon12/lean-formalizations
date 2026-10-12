import MeshOnly.MeshOnlyPowerGeometry

/-! The finite geometric region used by the local-power construction. -/

open scoped ENNReal

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

def meshOnlyBallCells (z : Euc d) (r : ℝ) : Set T.V :=
  {v | ((T.cell v).carrier ∩ Metric.closedBall z r).Nonempty}

lemma meshOnlyBallCells_finite (z : Euc d) (r : ℝ)
    (hD : Metric.closedBall z r ⊆ T.domain) :
    (T.meshOnlyBallCells z r).Finite :=
  T.locallyFinite _ (isCompact_closedBall z r) hD

lemma meshOnlyBallCells_cell_subset {z : Euc d} {r : ℝ} {v : T.V}
    (hv : v ∈ T.meshOnlyBallCells z r) (hmesh : T.mesh ≠ ∞) :
    (T.cell v).carrier ⊆ Metric.closedBall z (r + T.mesh.toReal) := by
  obtain ⟨y, hyv, hy⟩ := hv
  intro x hx
  apply Metric.mem_closedBall.mpr
  calc
    dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
    _ ≤ T.mesh.toReal + r := add_le_add
      (T.toTilingData.dist_le_mesh hx hyv hmesh) (Metric.mem_closedBall.mp hy)
    _ = r + T.mesh.toReal := add_comm _ _

lemma meshOnlyBallCells_cover {z : Euc d} {r : ℝ}
    (hD : Metric.closedBall z r ⊆ T.domain) {x : Euc d}
    (hx : x ∈ Metric.closedBall z r) :
    ∃ v ∈ T.meshOnlyBallCells z r, x ∈ (T.cell v).carrier := by
  obtain ⟨v, hv⟩ := T.toTilingData.exists_mem_cell (hD hx)
  exact ⟨v, ⟨x, hv, hx⟩, hv⟩

/-- Test functions supported in the chosen ball vanish on every contact with
an omitted cell. The finite region need not be neighbor-closed. -/
lemma meshOnlyBallCells_contact_cutoff {z : Euc d} {r : ℝ}
    (φ : Euc d → ℝ) (hφ : Function.support φ ⊆ Metric.closedBall z r)
    (v w : T.V) (hw : w ∉ T.meshOnlyBallCells z r) :
    ∀ x ∈ T.facet v w, φ x = 0 := by
  intro x hx
  by_contra hne
  exact hw ⟨x, hx.2, hφ hne⟩

end BouRabeeGwynne.OrthogonalTiling
