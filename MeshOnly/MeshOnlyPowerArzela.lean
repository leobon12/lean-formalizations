import MeshOnly.MeshOnlyPowerCompactness
import BouRabeeGwynne.PaperObjects
import Mathlib.Topology.MetricSpace.Lipschitz

/-! A compact-ball limit, with a genuine Lipschitz extension to the ambient
Euclidean space. Only pointwise convergence on the ball is needed later. -/

open scoped NNReal Topology BoundedContinuousFunction
open Filter

namespace BouRabeeGwynne

theorem meshOnly_exists_lipschitz_ball_limit {d : ℕ}
    (z : Euc d) (r : ℝ) (hr : 0 ≤ r) (C : ℝ≥0)
    (f : ℕ → Euc d → ℝ) (hzero : ∀ n, f n z = 0)
    (hlip : ∀ n, LipschitzOnWith C (f n) (Metric.closedBall z r)) :
    ∃ g : Euc d → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ LipschitzWith C g ∧
      g z = 0 ∧ ∀ x ∈ Metric.closedBall z r,
        Tendsto (fun n => f (σ n) x) atTop (𝓝 (g x)) := by
  classical
  let K := Metric.closedBall z r
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall z r)
  let F : ℕ → K →ᵇ ℝ := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f n x, (hlip n).continuousOn.restrict⟩
  have hF (n : ℕ) : LipschitzWith C (F n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hlip n).dist_le_mul x x.property y y.property
  have hbound (n : ℕ) (x : K) : |F n x| ≤ (C : ℝ) * r := by
    have h := (hlip n).dist_le_mul x x.property z (Metric.mem_closedBall_self hr)
    have hx : dist (x : Euc d) z ≤ r := Metric.mem_closedBall.mp x.property
    change dist (f n x) (f n z) ≤ _ at h
    rw [hzero n, Real.dist_eq, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left hx C.coe_nonneg)
  obtain ⟨g, σ, hσ, _, hg, hpoint⟩ :=
    meshOnly_compact_lipschitz_subsequence F C ((C : ℝ) * r) hF hbound
  let G : Euc d → ℝ := fun x => if hx : x ∈ K then g ⟨x, hx⟩ else 0
  have hG : LipschitzOnWith C G K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [G, dif_pos hx, dif_pos hy, Subtype.dist_eq] using hg.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨ψ, hψ, hψeq⟩ := hG.extend_real
  have hlim (x : Euc d) (hx : x ∈ K) :
      Tendsto (fun n => f (σ n) x) atTop (𝓝 (ψ x)) := by
    have heq : g ⟨x, hx⟩ = ψ x := by simpa only [G, dif_pos hx] using hψeq hx
    have hpt := hpoint ⟨x, hx⟩
    change Tendsto (fun n => f (σ n) x) atTop (𝓝 (g ⟨x, hx⟩)) at hpt
    exact heq ▸ hpt
  refine ⟨ψ, σ, hσ, hψ, ?_, hlim⟩
  have hz := hlim z (Metric.mem_closedBall_self hr)
  simp_rw [hzero] at hz
  exact tendsto_nhds_unique hz tendsto_const_nhds

end BouRabeeGwynne
