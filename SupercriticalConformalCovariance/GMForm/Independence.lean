import SupercriticalConformalCovariance.GMForm.ZeroBoundaryPullback
import SupercriticalConformalCovariance.Root.Field
import SupercriticalConformalCovariance.Domain.AeEq

set_option autoImplicit false
noncomputable section

open MeasureTheory TopologicalSpace Set Function
open LQGMetric (DistC DistOn)
open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GMForm

/-- Realizations on two extensions give the same metric after pullback to any
common measure-preserving refinement. Realization independence is supplied by
the proved `SupercriticalConformalCovariance.Domain` theorem underlying the sealed frozen anchor. -/
theorem metric_agrees_on_common_refinement
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U : Opens ℂ)
    {Ω Ω₁ Ω₂ Ωc : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] [MeasurableSpace Ωc]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) (Pc : Measure Ωc)
    [IsProbabilityMeasure Pc]
    (π₁ : Ω₁ → Ω) (π₂ : Ω₂ → Ω)
    (σ₁ : Ωc → Ω₁) (σ₂ : Ωc → Ω₂)
    (hπ₁ : MeasurePreserving π₁ P₁ P)
    (hπ₂ : MeasurePreserving π₂ P₂ P)
    (hσ₁ : MeasurePreserving σ₁ Pc P₁)
    (hσ₂ : MeasurePreserving σ₂ Pc P₂)
    (hbase : ∀ᵐ ω ∂Pc, π₁ (σ₁ ω) = π₂ (σ₂ ω))
    (h : Ω → DistOn U)
    (a₀ : Ω₁ → DistC) (a : Ω₁ → C(U, ℝ))
    (b₀ : Ω₂ → DistC) (b : Ω₂ → C(U, ℝ))
    (ha : IsDomainRealization U P₁ (h ∘ π₁) a₀ a)
    (hb : IsDomainRealization U P₂ (h ∘ π₂) b₀ b) :
    ∀ᵐ ω ∂Pc,
      domainMetric (ξ : ℝ) D U (a₀ (σ₁ ω)) (a (σ₁ ω)) =
        domainMetric (ξ : ℝ) D U (b₀ (σ₂ ω)) (b (σ₂ ω)) := by
  have haC := SupercriticalConformalCovariance.Root.isDomainRealization_comp hσ₁ ha
  have hbC := SupercriticalConformalCovariance.Root.isDomainRealization_comp hσ₂ hb
  have hbcongr : IsDomainRealization U Pc
      ((h ∘ π₁) ∘ σ₁) (b₀ ∘ σ₂) (b ∘ σ₂) := by
    apply SupercriticalConformalCovariance.Root.isDomainRealization_congr hbC
    · exact ha.1.comp hσ₁.measurable
    · filter_upwards [hbase] with ω hw
      exact congrArg h hw
  exact SupercriticalConformalCovariance.Domain.domainMetric_ae_eq_of_isDomainRealization ξ Q hQ D hD U Pc _ _ _ _ _ haC hbcongr

end SupercriticalConformalCovariance.GMForm
