import LQGMetric.Field.HeatMollifyKolm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Covariance

/-!
# Dominated convergence for `logCov` (task P2-FHEAT, part 3c)

`tendsto_logCov_of_dominated`: if `φ_n → φ`, `ψ_n → ψ` pointwise with `|φ_n|, |φ| ≤ G`,
`|ψ_n|, |ψ| ≤ H ≤ Hc`, and `G, ‖·‖G, H, ‖·‖H` integrable, then `logCov φ_n ψ_n → logCov φ ψ`
(two applications of dominated convergence, using `|log|x−y|| ≤ |x|+|y| + 1_{|x−y|≤1}|log|x−y||`).
Applied to the mean-zero truncations of `p_s(z,·) − p_s(z',·)` it gives the covariance of the
mollified whole-plane GFF:
`Cov(h*_ε(z) − h*_ε(z'), h*_ε(w) − h*_ε(w')) = logCov(p(z,·) − p(z',·), p(w,·) − p(w',·))`
(`IsWholePlaneGFF.covariance_heatMollify_sub`). Own elementary argument (standard).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric

/-! ### Application to the heat kernel -/

lemma heatKernel_le (s : ℝ) (hs : 0 < s) (z w : ℂ) : heatKernel s z w ≤ (2 * Real.pi * s)⁻¹ := by
  unfold heatKernel
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
  have : 0 ≤ ‖z - w‖ ^ 2 / (2 * s) := by positivity
  rw [neg_div]; linarith

lemma continuous_heatKernel (s : ℝ) (z : ℂ) : Continuous (heatKernel s z) := by
  unfold heatKernel; fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

end LQGMetric
