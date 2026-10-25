import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableCountableIdentity
import SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPLength

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem lfppLSCMetric_internal_le_lfppDOn
    (ξ : ℝ) (φ : C(ℂ, ℝ)) {U : Set ℂ}
    (x y : U) :
    (PfeWeyl.lfppLSCMetric ξ φ).internal U (x, y) ≤
      lfppDOn ξ φ U x y := by
  let C := lfppContMetric ξ φ φ.continuous
  let E := PfeWeyl.lfppLSCMetric ξ φ
  let f : C.Space → E.Space := id
  have hf : Isometry f := by
    intro u v
    exact PfeWeyl.edist_lfppLSCMetric_eq_cont ξ φ u v
  refine le_iInf fun P => ?_
  have hPc : ContinuousOn P.1 (Icc (0 : ℝ) 1) := P.2.1.continuousOn
  have hCurve : E.IsCurve P.1 0 1 := by
    refine ⟨zero_le_one, ?_⟩
    exact hf.continuous.comp_continuousOn
      ((continuous_weylPt C).comp_continuousOn hPc)
  have hlen : E.len P.1 0 1 ≤ lfppLen ξ φ P.1 := by
    have heq : E.len P.1 0 1 = C.len P.1 0 1 := by
      change eVariationOn (E.pt ∘ P.1) (Icc 0 1) =
        eVariationOn (C.pt ∘ P.1) (Icc 0 1)
      simpa only [one_mul] using
        (LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
          (F := E.pt ∘ P.1) (G := C.pt ∘ P.1) (c := 1)
          (fun s t => by
            rw [one_mul]
            exact PfeWeyl.edist_lfppLSCMetric_eq_cont ξ φ (P.1 s) (P.1 t))
          (Icc 0 1))
    rw [heq]
    exact len_le_lfppLen φ.continuous P.2.1 le_rfl le_rfl
  unfold LSCMetric.internal
  apply le_trans ?_ hlen
  apply iInf_le_of_le (P.1)
  apply iInf_le_of_le (0 : ℝ)
  apply iInf_le_of_le (1 : ℝ)
  apply iInf_le_of_le hCurve
  apply iInf_le_of_le P.2.2
  apply iInf_le_of_le P.2.1.source
  exact iInf_le_of_le P.2.1.target le_rfl

end SupercriticalLQGUniqueness.B2.PfeAxioms
