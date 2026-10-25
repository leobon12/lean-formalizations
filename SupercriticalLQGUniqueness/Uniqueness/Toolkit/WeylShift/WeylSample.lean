import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylBridge
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Cor
import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete




 





set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open LQGMetric (addFun IsGFFPlusCont)
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 


theorem ae_common_weyl_sample
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : LQGMetric.DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, Continuous (euclidForget (D (h ω))) ∧
      (D (h ω)).IsLengthSpace ∧
      ∀ g : C(ℂ, ℝ),
        weylScale (ξ : ℝ) g (D (h ω)) = (D (addFun (h ω) g)).1 := by
  have hplus : IsGFFPlusCont h P :=
    LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh.1
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  filter_upwards [BiLipschitz.Barrier.ae_curves_continuous hD hQ P h hh,
    hD.2.1 P h hplus, hD.2.2.2.1 P h hplus] with ω htop hlength hweyl
  exact ⟨htop.1, hlength, hweyl⟩

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift
