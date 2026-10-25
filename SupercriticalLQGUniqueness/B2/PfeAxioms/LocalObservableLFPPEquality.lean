import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPReverseCurve
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPUpper

 

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem lfppDOn_le_lfppLSCMetric_internal
    (ξ : ℝ) (φ : C(ℂ, ℝ)) {U : Set ℂ} (hU : IsOpen U)
    (x y : U) :
    lfppDOn ξ φ U x y ≤
      (PfeWeyl.lfppLSCMetric ξ φ).internal U (x, y) := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun htrace =>
    le_iInf fun hPa => le_iInf fun hPb => ?_
  rw [← hPa, ← hPb]
  exact lfppDOn_le_len_of_lfpp_curve ξ φ hU hP htrace

theorem lfppLSCMetric_internal_eq_lfppDOn
    (ξ : ℝ) (φ : C(ℂ, ℝ)) {U : Set ℂ} (hU : IsOpen U)
    (x y : U) :
    (PfeWeyl.lfppLSCMetric ξ φ).internal U (x, y) =
      lfppDOn ξ φ U x y := by
  exact le_antisymm
    (lfppLSCMetric_internal_le_lfppDOn ξ φ x y)
    (lfppDOn_le_lfppLSCMetric_internal ξ φ hU x y)

end SupercriticalLQGUniqueness.B2.PfeAxioms
