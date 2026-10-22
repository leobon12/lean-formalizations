import HigherDimLQGContinuity.Sewing.Intervals
import HigherDimLQGMetric.Metric.Internal
import Mathlib.Topology.Order.IntermediateValue

/-!
# Crossing bounds for the path sewing lemmas
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

/-- A path starting in the half ball and exiting the full ball crosses the sphere
at three quarters of the radius; its length pays the corresponding internal
set distance. -/
theorem sew_crossing_lower {d : ℕ} (R : HigherDimLQGMetric.ContMetric d)
    (P : ℝ → Rd d) {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (ha : ‖P a - z‖ < r / 2) (hb : ‖P b - z‖ = r) :
    HigherDimLQGMetric.setDistIn R Set.univ (sphere z (3 * r / 4)) (sphere z r) ≤
      R.len P a b := by
  have hf : ContinuousOn (fun u => ‖P u - z‖) (Icc a b) :=
    hP.sub continuousOn_const |>.norm
  have hlow : ‖P a - z‖ ≤ 3 * r / 4 := by linarith
  have hhigh : 3 * r / 4 ≤ ‖P b - z‖ := by rw [hb]; linarith
  obtain ⟨u, hu, hinner⟩ := intermediate_value_Icc hab hf ⟨hlow, hhigh⟩
  have huSphere : P u ∈ sphere z (3 * r / 4) := by
    rw [mem_sphere, dist_eq_norm]
    exact hinner
  have hbSphere : P b ∈ sphere z r := by
    rw [mem_sphere, dist_eq_norm]
    exact hb
  calc
    HigherDimLQGMetric.setDistIn R Set.univ (sphere z (3 * r / 4)) (sphere z r)
        ≤ R.internal Set.univ (P u) (P b) := by
          unfold HigherDimLQGMetric.setDistIn
          exact iInf_le_of_le (P u) (iInf_le_of_le huSphere
            (iInf_le_of_le (P b) (iInf_le_of_le hbSphere le_rfl)))
    _ ≤ R.len P u b := R.internal_le_len hu.2 (hP.mono (Icc_subset_Icc hu.1 le_rfl))
      (fun _ _ => Set.mem_univ _)
    _ ≤ R.len P a b := R.len_mono P hu.1 le_rfl

/-- The real cumulative-length coordinate of a finite-length path is additive on
subsegments. -/
theorem sew_cumulative_diff {d : ℕ} (R : HigherDimLQGMetric.ContMetric d)
    (P : ℝ → Rd d) (hfinite : R.len P 0 1 ≠ ⊤)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a ≤ b) :
    (R.len P 0 b).toReal - (R.len P 0 a).toReal = (R.len P a b).toReal := by
  have h0a : R.len P 0 a ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (R.len_mono P le_rfl ha.2)
  have habfin : R.len P a b ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (R.len_mono P ha.1 hb.2)
  have hreal := congrArg ENNReal.toReal (R.len_add P ha.1 hab)
  rw [ENNReal.toReal_add h0a habfin] at hreal
  linarith

theorem sew_cumulative_mono {d : ℕ} (R : HigherDimLQGMetric.ContMetric d)
    (P : ℝ → Rd d) (hfinite : R.len P 0 1 ≠ ⊤) :
    MonotoneOn (fun u : ℝ => (R.len P 0 u).toReal) (Icc 0 1) := by
  intro a ha b hb hab
  have h0b : R.len P 0 b ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (R.len_mono P le_rfl hb.2)
  exact ENNReal.toReal_mono h0b (R.len_mono P le_rfl hab)

end HigherDimLQGContinuity
