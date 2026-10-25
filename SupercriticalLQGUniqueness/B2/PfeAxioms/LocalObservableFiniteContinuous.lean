import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLocalizedNeighborhoodEvent
import SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPLength

 

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.MetricGeometry LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem continuousOn_lfppLSCMetric_internal
    (ξ : ℝ) (φ : C(ℂ, ℝ)) {U : Set ℂ} (hU : IsOpen U) :
    Continuous (fun p : U × U =>
      (PfeWeyl.lfppLSCMetric ξ φ).internal U (p.1, p.2)) := by
  classical
  let E := PfeWeyl.lfppLSCMetric ξ φ
  let C := lfppContMetric ξ φ φ.continuous
  let f : E.Space → C.Space := id
  have hf : Isometry f := by
    intro x y
    exact (PfeWeyl.edist_lfppLSCMetric_eq_cont ξ φ x y).symm
  let g : C.Space → E.Space := id
  have hg : Isometry g := by
    intro x y
    exact PfeWeyl.edist_lfppLSCMetric_eq_cont ξ φ x y
  have hEpt : Continuous E.pt :=
    hg.continuous.comp (continuous_weylPt C)
  have hopen : IsOpen (E.pt '' U) := by
    have heq : E.pt '' U = f ⁻¹' (C.pt '' U) := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, rfl⟩
      · rintro ⟨u, hu, h⟩
        exact ⟨u, hu, h⟩
    rw [heq]
    exact (C.isOpen_image_pt hU).preimage hf.continuous
  let j : U → E.pt '' U := fun z => ⟨E.pt z, z, z.2, rfl⟩
  have hj : Continuous j := (hEpt.comp continuous_subtype_val).subtype_mk _
  have hLen : IsLengthSpace E.Space := by
    apply isLengthSpace_iff_curves.mpr
    intro x y η hη
    obtain ⟨P, a, b, hab, hPc, hPa, hPb, hPLen⟩ :=
      isLengthSpace_iff_curves.mp
        (LQGMetric.LFPP.isLength_lfppContMetric φ.continuous)
          (f x) (f y) η hη
    let Q : ℝ → E.Space := fun t => P t
    have hQc : ContinuousOn Q (Icc a b) :=
      hg.continuous.comp_continuousOn hPc
    have hlen : curveLength Q a b = curveLength P a b := by
      change eVariationOn Q (Icc a b) = eVariationOn P (Icc a b)
      simpa only [one_mul] using
        (eVariationOn_eq_mul_of_edist
          (F := Q) (G := P) (c := 1)
          (fun s t => by
            rw [one_mul]
            exact PfeWeyl.edist_lfppLSCMetric_eq_cont ξ φ (Q s) (Q t))
          (Icc a b))
    rw [hf x y] at hPLen
    exact ⟨Q, a, b, hab, hQc, hPa, hPb, hlen.trans_le hPLen⟩
  have hc := InternalSpace.continuous_internalEDist hLen hopen
  convert hc.comp ((hj.comp continuous_fst).prodMk (hj.comp continuous_snd)) using 1
  funext p
  exact E.internal_eq_internalEDist U _

end SupercriticalLQGUniqueness.B2.PfeAxioms
