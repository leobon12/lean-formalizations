import SupercriticalLQGUniqueness.B2.PfeWeyl.NormalizedLFPP
import LQGMetric.LFPP.Length
import SLUMetricAPI2
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Regularity

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

private abbrev contLFPP (ξ : ℝ) (φ : C(ℂ, ℝ)) :=
  LQGMetric.LFPP.lfppContMetric ξ φ φ.continuous

private def toLSCSpace (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    (contLFPP ξ φ).Space → (lfppLSCMetric ξ φ).Space := id

private theorem isometry_toLSCSpace (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    Isometry (toLSCSpace ξ φ) := by
  intro x y
  exact edist_lfppLSCMetric_eq_cont ξ φ x y

private theorem lfppLSCMetric_len_eq_cont (ξ : ℝ) (φ : C(ℂ, ℝ))
    (P : ℝ → ℂ) (a b : ℝ) :
    (lfppLSCMetric ξ φ).len P a b = (contLFPP ξ φ).len P a b := by
  change eVariationOn ((lfppLSCMetric ξ φ).pt ∘ P) (Icc a b) =
    eVariationOn ((contLFPP ξ φ).pt ∘ P) (Icc a b)
  simpa only [one_mul] using
    (LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
      (F := (lfppLSCMetric ξ φ).pt ∘ P)
      (G := (contLFPP ξ φ).pt ∘ P) (c := 1)
      (fun s t => by
        rw [one_mul]
        exact edist_lfppLSCMetric_eq_cont ξ φ (P s) (P t)) (Icc a b))

 
theorem isLengthSpace_lfppLSCMetric (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    (lfppLSCMetric ξ φ).IsLengthSpace := by
  intro x y _ ε hε
  have hC := (LQGMetric.MetricGeometry.isLengthSpace_iff_curves.mp
    (LQGMetric.LFPP.isLength_lfppContMetric φ.continuous))
      ((contLFPP ξ φ).pt x) ((contLFPP ξ φ).pt y) ε hε
  obtain ⟨P, a, b, hab, hP, hPa, hPb, hlen⟩ := hC
  let Q : ℝ → ℂ := fun t => P t
  have hP' : (lfppLSCMetric ξ φ).IsCurve Q a b := by
    refine ⟨hab, ?_⟩
    exact (isometry_toLSCSpace ξ φ).continuous.comp_continuousOn hP
  refine ⟨Q, a, b, hP', hPa, hPb, ?_⟩
  rw [lfppLSCMetric_len_eq_cont]
  rw [← LSCMetric.edist_pt (lfppLSCMetric ξ φ) x y,
    edist_lfppLSCMetric_eq_cont]
  change (contLFPP ξ φ).len Q a b ≤
    edist ((contLFPP ξ φ).pt x) ((contLFPP ξ φ).pt y) + ENNReal.ofReal ε
  exact hlen

 

theorem isLengthSpace_normalizedLFPPMetric (ξ : ℝ)
    (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    (normalizedLFPPMetric ξ a φ).IsLengthSpace := by
  exact Uniqueness.Objects.Producer.isLengthSpace_of_scale
    (inv_pos.mpr (Set.mem_Ioi.mp a.property))
    (fun p => normalizedLFPPMetric_apply ξ a φ p)
    (isLengthSpace_lfppLSCMetric ξ φ)

end SupercriticalLQGUniqueness.B2.PfeWeyl
