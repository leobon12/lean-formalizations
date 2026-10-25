import SupercriticalLQGUniqueness.B2.DG20Lim.MidpointCompact
import LQGMetric.Metric.Midpoint

 

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def midpointError (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem midpointError_pos (n : ℕ) : 0 < midpointError n := by
  unfold midpointError
  positivity

theorem midpointError_le_one (n : ℕ) : midpointError n ≤ 1 := by
  unfold midpointError
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem midpointError_tendsto : Tendsto midpointError atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem exists_finite_approx_midpoints
    (D : ℕ → LQGMetric.ContMetric) (hlen : ∀ n, (D n).IsLength)
    (zn wn : ℕ → ℂ) :
    ∃ xn : ℕ → ℂ, ∀ n,
      (D n).1 (zn n, xn n) ≤
        (D n).1 (zn n, wn n) / 2 + midpointError n ∧
      (D n).1 (wn n, xn n) ≤
        (D n).1 (zn n, wn n) / 2 + midpointError n := by
  have hh : ∀ n, ∃ x : ℂ,
      (D n).1 (zn n, x) ≤
        (D n).1 (zn n, wn n) / 2 + midpointError n ∧
      (D n).1 (wn n, x) ≤
        (D n).1 (zn n, wn n) / 2 + midpointError n := by
    intro n
    obtain ⟨x, hx⟩ :=
      (LQGMetric.MetricGeometry.hasApproxMidpoints_of_isLengthSpace
        (hlen n)) ((D n).pt (zn n)) ((D n).pt (wn n))
        (midpointError n) (midpointError_pos n)
    rcases hx with ⟨h1, h2⟩
    refine ⟨(D n).unpt x, ?_, ?_⟩
    · rw [LQGMetric.ContMetric.dist_pt] at h1
      change dist ((D n).pt (zn n)) x ≤ _
      exact h1
    · rw [LQGMetric.ContMetric.dist_pt] at h2
      change dist ((D n).pt (wn n)) x ≤ _
      exact h2
  choose xn hxn using hh
  exact ⟨xn, hxn⟩

theorem approx_midpoint_short_left_leg
    (D : ℕ → LQGMetric.ContMetric) (zn wn xn : ℕ → ℂ)
    (hmid : ∀ n, (D n).1 (zn n, xn n) ≤
      (D n).1 (zn n, wn n) / 2 + midpointError n) (n : ℕ) :
    ENNReal.ofReal ((D n).1 (zn n, xn n)) ≤
      ENNReal.ofReal ((D n).1 (zn n, wn n)) + 1 := by
  have hn : 0 ≤ (D n).1 (zn n, wn n) := by
    rw [← (D n).dist_pt]
    exact dist_nonneg
  have hreal : (D n).1 (zn n, xn n) ≤ (D n).1 (zn n, wn n) + 1 := by
    have hε := midpointError_le_one n
    linarith [hmid n]
  calc
    ENNReal.ofReal ((D n).1 (zn n, xn n)) ≤
        ENNReal.ofReal ((D n).1 (zn n, wn n) + 1) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((D n).1 (zn n, wn n)) + 1 := by
      rw [ENNReal.ofReal_add hn (by norm_num)]
      norm_num

end SupercriticalLQGUniqueness.B2.DG20Lim
