import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPBall
import LQGMetric.Papers.DDDF.RSWPath

 







set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem lfppDOn_self_of_mem {ξ : ℝ} {φ : ℂ → ℝ}
    {U : Set ℂ} {x : ℂ} (hx : x ∈ U) :
    lfppDOn ξ φ U x x = 0 := by
  apply le_antisymm _ bot_le
  calc
    lfppDOn ξ φ U x x ≤ lfppLen ξ φ (fun _ => x) :=
      lfppDOn_le (LQGMetric.DDDF.isPiecewiseC1Path_const x) (fun _ _ => hx)
    _ = 0 := LQGMetric.DDDF.lfppLen_const x

theorem lfppDOn_le_sum_of_vertices {ξ : ℝ} {φ : ℂ → ℝ}
    {U : Set ℂ} (v : ℕ → ℂ) (hv : ∀ i, v i ∈ U) (N : ℕ) :
    lfppDOn ξ φ U (v 0) (v N) ≤
      ∑ i ∈ Finset.range N, lfppDOn ξ φ U (v i) (v (i + 1)) := by
  induction N with
  | zero => simpa using (lfppDOn_self_of_mem (hv 0)).le
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact (lfppDOn_triangle (v 0) (v N) (v (N + 1))).trans
        (add_le_add ih le_rfl)

end SupercriticalLQGUniqueness.B2.PfeAxioms
