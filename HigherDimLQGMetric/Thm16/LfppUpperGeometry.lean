import HigherDimLQGMetric.Sec4.Basic
import HigherDimLQGMetric.DGZ.FunctionalsBounds
import HigherDimLQGMetric.Config.Geometry

/-! The LFPP sphere diameter bounds pointwise internal LFPP in a larger domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l9c_lfppDistIn_le_sphereDiam {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d)
    (hφ : Continuous (convMollify κ ε h))
    {r : ℝ} (hr : 0 < r) {U : Set (Rd d)}
    (hU : ann (0 : Rd d) (r / 2) (2 * r) ⊆ U)
    {z w : Rd d} (hz : z ∈ sphere (0 : Rd d) r)
    (hw : w ∈ sphere (0 : Rd d) r) :
    lfppDistIn κ ξ ε h U z w ≤
      ENNReal.ofReal (DGZ.lfppDiam ξ (convMollify κ ε h)
        (sphere (0 : Rd d) r) (ann 0 (r / 2) (2 * r))) := by
  let V : Set (Rd d) := ann 0 (r / 2) (2 * r)
  have hVopen : IsOpen V := isOpen_ann _ _ _
  have hVc : IsPreconnected V :=
    (config_isConnected_ann hd 0 (half_pos hr) (by linarith)).2
  have hSV : sphere (0 : Rd d) r ⊆ V := by
    intro x hx
    have hx' : ‖x‖ = r := by simpa only [mem_sphere, dist_eq_norm, sub_zero] using hx
    dsimp [V, ann]
    simpa only [sub_zero, hx'] using
      (show r / 2 < ‖x‖ ∧ ‖x‖ < 2 * r by rw [hx']; constructor <;> linarith)
  have hj : HigherDimLFPP.PcwJoined V z w :=
    DGZ.pcwJoined_of_isPreconnected hVopen hVc (hSV hz) (hSV hw)
  have hbdd := DGZ.bddAbove_lfppDiam_of_isCompact hVopen hVc hφ ξ
    (isCompact_sphere (0 : Rd d) r) hSV subset_rfl
  calc
    lfppDistIn κ ξ ε h U z w = fieldDistIn ξ (convMollify κ ε h) U z w := rfl
    _ ≤ fieldDistIn ξ (convMollify κ ε h) V z w := fieldDistIn_mono hU
    _ = ENNReal.ofReal (HigherDimLFPP.lfppDistOn ξ (convMollify κ ε h) V z w) :=
      fieldDistIn_eq_ofReal hφ hj
    _ ≤ ENNReal.ofReal (DGZ.lfppDiam ξ (convMollify κ ε h)
          (sphere (0 : Rd d) r) V) :=
      ENNReal.ofReal_le_ofReal (DGZ.lfppDistOn_le_lfppDiam hbdd hz hw)

end HigherDimLQGMetric
