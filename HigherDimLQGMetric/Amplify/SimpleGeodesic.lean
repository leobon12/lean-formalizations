import HigherDimLQGMetric.Amplify.Defs
import HigherDimLQGMetric.Metric.Internal

/-! Reparametrizing a proper length metric geodesic as a simple arc. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Topology
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

variable {d : ℕ}

/-- Distinct endpoints of a proper length metric have a simple geodesic arc. -/
theorem amplify_exists_simple_geodesic (D : ContMetric d) (hD : D.IsLength)
    [ProperSpace D.Space] {u v : Rd d} (huv : u ≠ v) :
    ∃ γ : ℝ → Rd d, IsSimpleArc γ ∧ γ 0 = u ∧ γ 1 = v ∧
      D.len γ 0 1 = ENNReal.ofReal (D.1 (u, v)) := by
  obtain ⟨P, hP0, hPT, hgeo, _, hdist⟩ := D.exists_geodesic hD u v
  let T : ℝ := D.1 (u, v)
  have hT : 0 < T := D.apply_pos huv
  let γ : ℝ → Rd d := fun t => P (T * t)
  have hmap : MapsTo (fun t : ℝ => T * t) (Icc 0 1) (Icc 0 T) := by
    intro t ht
    exact ⟨mul_nonneg hT.le ht.1, mul_le_of_le_one_right hT.le ht.2⟩
  have hPc : ContinuousOn P (Icc 0 T) :=
    D.continuousOn_pt_comp_iff.1 hgeo.2.1
  have hγc : ContinuousOn γ (Icc 0 1) :=
    hPc.comp (by fun_prop) hmap
  have hγi : InjOn γ (Icc 0 1) := by
    intro s hs t ht heq
    have hval := hdist (T * s) (hmap hs) (T * t) (hmap ht)
    have hzero : |T * t - T * s| = 0 := by
      change P (T * s) = P (T * t) at heq
      rw [← hval, heq, D.apply_self]
    have hmul : T * t = T * s := sub_eq_zero.mp (abs_eq_zero.mp hzero)
    exact mul_left_cancel₀ hT.ne' hmul.symm
  refine ⟨γ, ⟨hγc, hγi⟩, ?_, ?_, ?_⟩
  · simpa only [γ, mul_zero] using hP0
  · simpa only [γ, mul_one] using hPT
  · have hmono : MonotoneOn (fun t : ℝ => T * t) (Icc 0 1) := by
      intro s _ t _ hst
      exact mul_le_mul_of_nonneg_left hst hT.le
    change curveLength ((D.pt ∘ P) ∘ fun t : ℝ => T * t) 0 1 = _
    rw [curveLength_comp_of_continuousOn_monotoneOn _ zero_le_one
      (by fun_prop) hmono]
    simpa only [mul_zero, mul_one, Function.comp_apply, hP0, hPT,
      D.edist_pt] using hgeo.2.2

end HigherDimLQGMetric
