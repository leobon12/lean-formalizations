import MeshOnly.MeshOnlyPowerWeights
import BouRabeeGwynne.TilingNetwork
import MeshOnly.MeshOnlyHeatGenerator
import MeshOnly.MeshOnlyCellMass

/-! The locally constructed power weights satisfy the exact unnormalized clock
identity at every vertex whose two-mesh neighborhood fits inside the power ball. -/

open scoped ENNReal

namespace BouRabeeGwynne.OrthogonalTiling

theorem exists_meshOnly_local_clock_potential {n : ℕ}
    (T : OrthogonalTiling (n + 1)) (z : Euc (n + 1)) (r ρ β : ℝ)
    (hρ : 0 < ρ) (hρr : ρ < r) (hmesh : T.mesh ≠ ⊤)
    (hβ : β + 2 * T.mesh.toReal < ρ)
    (hcollar : Metric.closedBall z (r + T.mesh.toReal) ⊆ interior T.domain) :
    ∃ ω : T.V → ℝ,
      (∀ v w, T.pos v ∈ Metric.ball z ρ → T.pos w ∈ Metric.ball z ρ →
        |ω w - ω v| ≤ (2 * T.mesh.toReal) * ‖T.pos w - T.pos v‖) ∧
      (∀ v, T.pos v ∈ Metric.ball z β → ∀ hv : (T.neighbors v).Finite,
        T.discreteLaplacian (fun u => ‖T.pos u - z‖ ^ 2 - ω u) v hv =
          2 * ((n + 1 : ℕ) : ℝ) * (T.cell v).volume.toReal) := by
  classical
  obtain ⟨ω, hω, hωlip⟩ :=
    T.exists_meshOnly_local_power_weights z r ρ hρ hρr hmesh hcollar
  refine ⟨ω, hωlip, ?_⟩
  intro v hv hvfinite
  have hvρ : T.pos v ∈ Metric.ball z ρ := by
    apply Metric.ball_subset_ball (show β ≤ ρ by have : 0 ≤ T.mesh.toReal := ENNReal.toReal_nonneg; linarith) hv
  have hvR : v ∈ T.meshOnlyBallCells z r := by
    refine ⟨T.pos v, interior_subset (T.pos_mem_interior v), ?_⟩
    exact Metric.closedBall_subset_closedBall hρr.le (Metric.ball_subset_closedBall hvρ)
  have hvD : (T.cell v).carrier ⊆ interior T.domain :=
    (T.meshOnlyBallCells_cell_subset hvR hmesh).trans hcollar
  apply T.discreteLaplacian_correctedSquare (by omega) v hvD hvfinite ω
  intro w hvw
  have hwρ : T.pos w ∈ Metric.ball z ρ := by
    apply Metric.mem_ball.mpr
    have he := T.toTilingData.edge_dist_le_two_mesh hvw hmesh
    have hv' := Metric.mem_ball.mp hv
    calc
      dist (T.pos w) z ≤ dist (T.pos w) (T.pos v) + dist (T.pos v) z := dist_triangle _ _ _
      _ < ρ := by rw [dist_comm (T.pos w) (T.pos v)]; linarith
  apply hω v w hvw hvρ hwρ
  obtain ⟨y, hy⟩ := hvw.2.1
  refine ⟨y, hy, ?_⟩
  apply Metric.mem_ball.mpr
  have hyv := T.toTilingData.dist_pos_le_mesh hy.1 hmesh
  have hv' := Metric.mem_ball.mp hv
  have hm : 0 ≤ T.mesh.toReal := ENNReal.toReal_nonneg
  calc
    dist y z ≤ dist y (T.pos v) + dist (T.pos v) z := dist_triangle _ _ _
    _ < ρ := by linarith

/-- The same constructed local potential has drift exactly `2d` under the
actual tile-volume generator of every finite network retaining the neighbors
of the active vertex. -/
theorem exists_meshOnly_finiteNetwork_clock_potential {n : ℕ}
    (T : OrthogonalTiling (n + 1)) (z : Euc (n + 1)) (r ρ β : ℝ)
    (hρ : 0 < ρ) (hρr : ρ < r) (hmesh : T.mesh ≠ ⊤)
    (hβ : β + 2 * T.mesh.toReal < ρ)
    (hcollar : Metric.closedBall z (r + T.mesh.toReal) ⊆ interior T.domain)
    (R : Set T.V) [Fintype R] :
    ∃ ω : T.V → ℝ,
      (∀ v w, T.pos v ∈ Metric.ball z ρ → T.pos w ∈ Metric.ball z ρ →
        |ω w - ω v| ≤ (2 * T.mesh.toReal) * ‖T.pos w - T.pos v‖) ∧
      (∀ v : R, T.pos v ∈ Metric.ball z β → T.neighbors v ⊆ R →
        (T.finiteNetwork R).massGenerator (fun w => (T.cell w).volume.toReal)
          (fun w => ‖T.pos w - z‖ ^ 2 - ω w) v = 2 * ((n + 1 : ℕ) : ℝ)) := by
  classical
  obtain ⟨ω, hωlip, hωclock⟩ :=
    T.exists_meshOnly_local_clock_potential z r ρ β hρ hρr hmesh hβ hcollar
  refine ⟨ω, hωlip, ?_⟩
  intro v hv hneighbors
  have hvfinite : (T.neighbors v).Finite := (Set.toFinite R).subset hneighbors
  have hm := T.meshOnly_cellVolume_toReal_pos v
  unfold FiniteConductanceNetwork.massGenerator
  rw [T.finiteNetwork_laplacian R (fun u : T.V => ‖T.pos u - z‖ ^ 2 - ω u)
    v hvfinite hneighbors, hωclock v hv hvfinite]
  exact mul_div_cancel_right₀ _ hm.ne'

end BouRabeeGwynne.OrthogonalTiling
