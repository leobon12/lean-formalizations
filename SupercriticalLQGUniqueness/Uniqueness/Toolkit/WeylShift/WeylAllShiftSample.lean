import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylSample
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylLocalTopology




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift
open LQGMetric (DistC addFun)

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

theorem ae_all_shift_curves
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ g : C(ℂ, ℝ),
      Continuous (euclidForget (D (addFun (h ω) g))) ∧
      ∀ (C : ℝ → ℂ) (a b : ℝ),
        (D (addFun (h ω) g)).IsCurve C a b →
        (D (h ω)).IsCurve C a b ∧ ContinuousOn C (Icc a b) := by
  filter_upwards [ae_common_weyl_sample hD P h hh] with ω hω
  intro g
  let E : LSCMetric := D (addFun (h ω) g)
  let D₀ : LSCMetric := D (h ω)
  have hW : ∀ q : ℂ × ℂ, E q = weylScale (ξ : ℝ) g D₀ q := by
    intro q
    exact (congrFun (hω.2.2 g) q).symm
  have hEcont : Continuous (euclidForget E) :=
    continuous_forget_of_weyl D₀ E (ξ : ℝ) ξ.2.le g hω.1 hW
  refine ⟨hEcont, ?_⟩
  intro C a b hC
  exact ⟨curve_back_all_continuous D₀ E (ξ : ℝ) ξ.2.le g hω.1 hW hC,
    hEcont.comp_continuousOn hC.2⟩

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift
