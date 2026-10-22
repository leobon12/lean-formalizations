import HigherDimLQGMetric.LfppTight.PureShellUniform
import HigherDimLQGMetric.Select.MetricBorel

/-! Finite shell covers give the uniform separation test for continuous metrics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_metricSep_of_shell {d : ℕ} (R m k : ℕ)
    (T : Finset (Rd d)) (D : C(Rd d × Rd d, ℝ))
    (ρ t : ℝ) (hρ : ρ = 1 / (8 * ((m : ℝ) + 1)))
    (ht : 1 / ((k : ℝ) + 1) ≤ t)
    (hcover : closedBall (0 : Rd d) R ⊆ ⋃ c ∈ T, ball c ρ)
    (hbarrier : ∀ c ∈ T, ∀ x ∈ closedBall c (2 * ρ),
      ∀ y ∉ ball c (4 * ρ),
        DGZ.nd_setInf (sphere c (2 * ρ)) (sphere c (4 * ρ)) D ≤ D (x, y))
    (hgood : ∀ c ∈ T,
      t < DGZ.nd_setInf (sphere c (2 * ρ)) (sphere c (4 * ρ)) D) :
    D ∈ metricSepSet_select R m k := by
  intro x hx y hxy
  obtain ⟨c, hcT, hcx⟩ := by
    simpa only [mem_iUnion, exists_prop] using hcover hx
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hxc : x ∈ closedBall c (2 * ρ) := by
    rw [mem_closedBall]
    have hh : dist x c < ρ := by simpa only [mem_ball, dist_comm] using hcx
    linarith
  have hyc : y ∉ ball c (4 * ρ) := by
    intro hy
    have h1 : dist x c < ρ := by simpa only [mem_ball, dist_comm] using hcx
    have h2 : dist y c < 4 * ρ := by simpa only [mem_ball, dist_comm] using hy
    have h3 := dist_triangle y c x
    have hsep : 1 / ((m : ℝ) + 1) = 8 * ρ := by
      rw [hρ]
      field_simp
    rw [dist_eq_norm] at h3
    rw [dist_comm c x] at h3
    rw [hsep] at hxy
    linarith [h3, norm_sub_rev y x]
  exact ht.trans ((hgood c hcT).le.trans (hbarrier c hcT x hxc y hyc))

theorem l6a_normMetric_shell_barrier {d : ℕ} (ξ a : ℝ)
    (φ : Rd d → ℝ) (hφ : Continuous φ) (ha : 0 < a)
    (c : Rd d) {r₁ r₂ : ℝ} (hr : r₂ < r₁)
    {x y : Rd d} (hx : x ∈ closedBall c r₂) (hy : y ∉ ball c r₁) :
    DGZ.nd_setInf (sphere c r₂) (sphere c r₁) (DGZ.normMetricC ξ φ a) ≤
      DGZ.normMetricC ξ φ a (x, y) := by
  rw [DGZ.nd_setInf_normMetricC hφ ha,
    DGZ.normMetricC_apply hφ]
  exact mul_le_mul_of_nonneg_left
    (DGZ.lfppSetDist_sphere_le_lfppDistOn hφ hr hx hy
      (HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ _) (mem_univ _)))
    (inv_pos.mpr ha).le

end HigherDimLQGMetric
