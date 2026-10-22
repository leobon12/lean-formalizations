import HigherDimLQGMetric.Proper.Scale
import HigherDimLQGMetric.Metric.Internal
import LQGMetric.Metric.LengthSpace
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Escape from Euclidean balls in a length metric

Every short path from the origin to a point outside a Euclidean ball meets its sphere.
This deterministic observation converts lower bounds on sphere distances into properness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- A sphere whose points are all farther than `M` in a length metric blocks the metric ball of
radius `M` around the origin. -/
theorem proper_norm_lt_of_dist_lt_sphere (D : ContMetric d) (hL : D.IsLength)
    {R M : ℝ} (hR : 0 < R)
    (hS : ∀ v : Rd d, ‖v‖ = R → M < D.1 (0, v))
    {x : Rd d} (hx : D.1 (0, x) < M) : ‖x‖ < R := by
  by_contra hnot
  have hxR : R ≤ ‖x‖ := le_of_not_gt hnot
  have hM : 0 < M := (D.nonneg 0 x).trans_lt hx
  let ε := (M - D.1 (0, x)) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨γ, hγ⟩ := hL (D.pt 0) (D.pt x) ε hε
  have hcont : ContinuousOn (fun t : ℝ => ‖D.unpt (γ.extend t)‖) (Icc 0 1) :=
    ((D.continuous_unpt.comp γ.continuous_extend).norm).continuousOn
  have h0 : ‖D.unpt (γ.extend 0)‖ = 0 := by
    rw [Path.extend_zero]
    simp only [D.unpt_pt, norm_zero]
  have h1 : ‖D.unpt (γ.extend 1)‖ = ‖x‖ := by
    rw [Path.extend_one, D.unpt_pt]
  obtain ⟨t, ht, htR⟩ := intermediate_value_Icc (zero_le_one' ℝ) hcont
    (show R ∈ Icc (‖D.unpt (γ.extend 0)‖) (‖D.unpt (γ.extend 1)‖) by
      rw [h0, h1]
      exact ⟨hR.le, hxR⟩)
  let v : Rd d := D.unpt (γ.extend t)
  have hvR : ‖v‖ = R := htR
  have hdist : ENNReal.ofReal (D.1 (0, v)) ≤ pathLength γ := by
    rw [← D.edist_pt]
    calc
      edist (D.pt 0) (D.pt v) = edist (γ.extend 0) (γ.extend t) := by
        rw [Path.extend_zero]
        rfl
      _ ≤ curveLength γ.extend 0 t := edist_le_curveLength γ.extend ht.1
      _ ≤ pathLength γ := curveLength_mono γ.extend le_rfl ht.2
  have hsum : ENNReal.ofReal (D.1 (0, x)) + ENNReal.ofReal ε =
      ENNReal.ofReal (D.1 (0, x) + ε) := by
    rw [ENNReal.ofReal_add (D.nonneg 0 x) hε.le]
  have hbound : pathLength γ < ENNReal.ofReal M := by
    calc
      pathLength γ ≤ edist (D.pt 0) (D.pt x) + ENNReal.ofReal ε := hγ
      _ = ENNReal.ofReal (D.1 (0, x) + ε) := by
        rw [D.edist_pt, hsum]
      _ < ENNReal.ofReal M := (ENNReal.ofReal_lt_ofReal_iff hM).2 (by
        dsimp [ε]
        linarith)
  have hcontra : D.1 (0, v) < M := (ENNReal.ofReal_lt_ofReal_iff hM).1
    (hdist.trans_lt hbound)
  exact (not_lt_of_ge (hS v hvR).le) hcontra

/-- Escape of all large metric balls through Euclidean spheres implies properness. -/
theorem properSpace_of_sphere_growth (D : ContMetric d) (hL : D.IsLength)
    (hG : ∀ M : ℝ, ∃ R : ℝ, 0 < R ∧
      ∀ v : Rd d, ‖v‖ = R → M < D.1 (0, v)) : ProperSpace D.Space := by
  refine ⟨fun x r => ?_⟩
  obtain ⟨R, hR, hS⟩ := hG (D.1 (0, D.unpt x) + r + 1)
  have hA : IsCompact (D.pt ⁻¹' Metric.closedBall x r) := by
    refine (isCompact_closedBall (0 : Rd d) R).of_isClosed_subset
      (Metric.isClosed_closedBall.preimage D.continuous_pt) ?_
    intro v hv
    have hv' : D.1 (D.unpt x, v) ≤ r := by
      have hv0 := Metric.mem_closedBall.mp hv
      change D.1 (v, D.unpt x) ≤ r at hv0
      simpa only [D.apply_comm] using hv0
    have htri := D.apply_triangle 0 (D.unpt x) v
    have hlt : D.1 (0, v) < D.1 (0, D.unpt x) + r + 1 := by linarith
    have hn := proper_norm_lt_of_dist_lt_sphere D hL hR hS hlt
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hn.le)
  have himg := hA.image D.continuous_pt
  rwa [Set.image_preimage_eq _ (fun y => ⟨D.unpt y, rfl⟩)] at himg

end HigherDimLQGMetric
