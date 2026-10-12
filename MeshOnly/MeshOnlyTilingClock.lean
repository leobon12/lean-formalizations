import MeshOnly.MeshOnlyPowerClock
import MeshOnly.MeshOnlyCellMass
import MeshOnly.MeshOnlyClockCrossing

/-! The ball-crossing estimate for an actual orthogonal tiling and its actual
volume-clock law. The local power weights are constructed from the geometry. -/

open MeasureTheory
open scoped Classical NNReal ENNReal

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

theorem meshOnly_local_ball_crossing_le (R : Set T.V) [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    (S : Set R) (x : R) {r : ℝ} (hr : 0 < r) (hmesh : T.mesh ≠ ∞)
    (hsmall : 2 * T.mesh.toReal < r)
    (hcollar : Metric.closedBall (T.pos x) (3 * r + T.mesh.toReal) ⊆ interior T.domain)
    (hS : ∀ v ∈ S, dist (T.pos v) (T.pos x) < r)
    (hneighbors : ∀ v ∈ S, ∀ w : T.V, T.adj v w → w ∈ R) (t : ℝ≥0) :
    ((T.finiteNetwork R).poissonizedUniformizedLaw
      (fun v : R => (T.cell v).volume.toReal)
      (fun v => T.meshOnly_cellVolume_toReal_pos v) S x t
      {w | r ≤ dist (T.pos w) (T.pos x)}).toReal ≤
        (2 * ((n + 1 : ℕ) : ℝ) * (t : ℝ) +
          2 * T.mesh.toReal * (r + 2 * T.mesh.toReal)) / r ^ 2 := by
  let N := T.finiteNetwork R
  let m : R → ℝ := fun v => (T.cell v).volume.toReal
  have hm : ∀ v, 0 < m v := fun v => T.meshOnly_cellVolume_toReal_pos v
  let z := T.pos x
  let K : Set R := {v | dist (T.pos v) z ≤ r + 2 * T.mesh.toReal}
  have hε : 0 ≤ T.mesh.toReal := ENNReal.toReal_nonneg
  obtain ⟨ω, hωlip, hωclock⟩ :=
    T.exists_meshOnly_finiteNetwork_clock_potential z (3*r) (2*r) r
      (by positivity) (by linarith) hmesh (by linarith) hcollar R
  have hKx : x ∈ K := by dsimp [K, z]; simp only [dist_self]; positivity
  have hK : ∀ v ∈ K, v ∈ S → ∀ w, N.a v w ≠ 0 → w ∈ K := by
    intro v _ hv w ha
    have hpos : 0 < N.a v w := lt_of_le_of_ne (N.nonneg v w) (Ne.symm ha)
    have hadj : T.adj v w := T.conductanceReal_pos_iff.mp hpos
    have hstep := T.toTilingData.edge_dist_le_two_mesh hadj hmesh
    have hvball := hS v hv
    change dist (T.pos w) z ≤ r + 2 * T.mesh.toReal
    calc
      _ ≤ dist (T.pos w) (T.pos v) + dist (T.pos v) z := dist_triangle _ _ _
      _ ≤ _ := by rw [dist_comm (T.pos w) (T.pos v)]; dsimp [z]; linarith
  let q : R → ℝ := fun v => ‖T.pos v - z‖ ^ 2
  let ωR : R → ℝ := fun v => ω v
  have hgen : ∀ v ∈ S, N.massGenerator m (q - ωR) v ≤
      2 * ((n + 1 : ℕ) : ℝ) := by
    intro v hv
    have h := hωclock v (Metric.mem_ball.mpr (hS v hv)) (hneighbors v hv)
    exact h.le
  have hω : ∀ᵐ w ∂N.poissonizedUniformizedLaw m hm S x t,
      ωR w - ωR x ≤ 2 * T.mesh.toReal * (r + 2 * T.mesh.toReal) := by
    filter_upwards [N.poissonizedUniformizedLaw_ae_mem m hm S K hK hKx t] with w hw
    have hxball : T.pos x ∈ Metric.ball z (2*r) := by
      apply Metric.mem_ball.mpr
      dsimp [z]
      simp only [dist_self]
      positivity
    have hwball : T.pos w ∈ Metric.ball z (2*r) := by
      apply Metric.mem_ball.mpr
      change dist (T.pos w) z ≤ r + 2 * T.mesh.toReal at hw
      linarith
    have hdist : ‖T.pos w - T.pos x‖ ≤ r + 2 * T.mesh.toReal := by
      simpa only [K, Set.mem_setOf_eq, z, dist_eq_norm] using hw
    exact (le_abs_self (ωR w - ωR x)).trans
      ((hωlip x w hxball hwball).trans
        (mul_le_mul_of_nonneg_left hdist (by positivity)))
  have h := N.poissonizedUniformizedLaw_crossing_le m hm S q ωR
    (v := x) (by simp [q, z]) (fun v => sq_nonneg _)
    (b := 2 * ((n + 1 : ℕ) : ℝ)) (A := 2 * T.mesh.toReal * (r + 2 * T.mesh.toReal))
    (by positivity) hr hgen t hω
  have hevent : {w : R | r ^ 2 ≤ q w} = {w : R | r ≤ dist (T.pos w) (T.pos x)} := by
    apply Set.ext
    intro w
    change (r ^ 2 ≤ ‖T.pos w - z‖ ^ 2) ↔ r ≤ dist (T.pos w) (T.pos x)
    rw [dist_eq_norm]
    exact sq_le_sq₀ hr.le (norm_nonneg _)
  rw [hevent] at h
  exact h

end BouRabeeGwynne.OrthogonalTiling
