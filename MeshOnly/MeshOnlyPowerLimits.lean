import MeshOnly.MeshOnlyPowerMollification
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! The constructed smooth fields converge locally uniformly on every cell
interior. This is the derivative convergence needed for the compact-ball
Poincaré limit, and avoids a separate weak-gradient limit theorem. -/

open scoped Topology
open Filter

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

theorem meshOnlyMollifiedDisplacement_tendstoLocallyUniformlyOn
    (R : Set T.V) [Fintype R] (v : R)
    {ι : Type*} {l : Filter ι} (φ : ι → ContDiffBump (0 : Euc d))
    (hφ : Tendsto (fun n => (φ n).rOut) l (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun n => T.meshOnlyMollifiedDisplacement R (φ n))
      (fun x => (2 : ℝ) • (x - T.pos v)) l (interior (T.cell v).carrier) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  refine ⟨Metric.ball x (r / 2),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (half_pos hr)), ?_⟩
  filter_upwards [hφ.eventually (gt_mem_nhds (half_pos hr)),
    hφ.eventually (gt_mem_nhds (half_pos hε))] with n hnr hnε
  intro y hy
  have hsub : Metric.ball y (φ n).rOut ⊆ interior (T.cell v).carrier := by
    intro t ht
    apply hball
    apply Metric.mem_ball.mpr
    have ht' := Metric.mem_ball.mp ht
    have hy' := Metric.mem_ball.mp hy
    calc
      dist t x ≤ dist t y + dist y x := dist_triangle _ _ _
      _ < r := by linarith
  have h := T.meshOnlyMollifiedDisplacement_dist_le_of_ball_subset R v (φ n) y hsub
  rw [dist_comm]
  exact lt_of_le_of_lt h (by linarith)

end BouRabeeGwynne.OrthogonalTiling
