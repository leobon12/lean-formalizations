import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedMollifierSigma
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPEquality
import LQGMetric.Metric.InternalOps

 



set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.MetricGeometry

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem lfppContMetric_internal_eq_lfppDOn
    (ξ : ℝ) (φ : C(ℂ, ℝ)) {U : Set ℂ} (hU : IsOpen U) (x y : U) :
    (lfppContMetric ξ φ φ.continuous).internal U x y =
      lfppDOn ξ φ U x y := by
  let C := lfppContMetric ξ φ φ.continuous
  let E := B2.PfeWeyl.lfppLSCMetric ξ φ
  have h : E.internal U (x, y) = C.internal U x y := by
    have he := internalEDist_image_of_edist_eq
      (X := C.Space) (Z := E.Space) (Equiv.refl ℂ)
      one_ne_zero ENNReal.one_ne_top
      (fun a b => by
        rw [one_mul]
        exact B2.PfeWeyl.edist_lfppLSCMetric_eq_cont ξ φ a b)
      (C.pt '' U) x.1 y.1
    rw [LSCMetric.internal_eq_internalEDist]
    unfold ContMetric.internal
    convert he using 2
    · ext z
      simp only [E, C, LSCMetric.pt, ContMetric.pt, Set.mem_image]
      aesop
    · rfl
    · rfl
    · simp [ContMetric.pt]
  rw [← h]
  exact B2.PfeAxioms.lfppLSCMetric_internal_eq_lfppDOn ξ φ hU x y

end SupercriticalLQGUniqueness.B2.DG20Lim
