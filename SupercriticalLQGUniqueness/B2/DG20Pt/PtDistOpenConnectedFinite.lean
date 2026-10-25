import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGeometricBudget
import LQGMetric.Papers.DG.S3T15
import LQGMetric.Papers.DDDF.P10Tail

 


set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_internal_finite_of_open_connected
    (ξ : ℝ) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) :
    lfppDOn ξ φ U z w ≠ ∞ := by
  obtain ⟨q, hq⟩ := LQGMetric.DG.t15_exists_isDGPath hU hUc hz hw
  have hp : IsPiecewiseC1Path q z w :=
    ⟨hq.source, hq.target, hq.continuousOn, hq.piecewise_contDiff⟩
  let K : Set ℂ := q '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hq.continuousOn
  have hAdm : LQGMetric.DDDF.AdmPath K {z} {w} q := by
    refine ⟨z, by simp, w, by simp, hp, ?_⟩
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hfin : lfppLen ξ φ q ≠ ∞ :=
    LQGMetric.DDDF.lfppLen_ne_top_of_adm hφ hK hAdm
  exact ne_top_of_le_ne_top hfin (lfppDOn_le hp hq.mapsTo)

end SupercriticalLQGUniqueness.B2.DG20Pt
