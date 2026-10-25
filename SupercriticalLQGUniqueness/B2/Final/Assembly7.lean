import SupercriticalLQGUniqueness.B2.Final.Assembly6
import SupercriticalLQGUniqueness.B2.PfeLocal.R68LocSite

 









set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC IsGFFPlusCont IsGFFPlusBddCont)

namespace SupercriticalLQGUniqueness.B2.Final

 


theorem theorems_1_3_and_1_8i_of_identification (h : S2IdentificationSite) :
    (∀ ξ : Set.Ioi (0 : ℝ), ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        ∃ L : Ω → LSCMetric, Measurable L ∧
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (L ω).toLSCFun.1)) ∧
    (∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∃ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D ∧
        ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusBddCont h P →
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (D (h ω)).toLSCFun.1)) :=
  theorems_1_3_and_1_8i_of_3bnew ⟨h, PfeLocal.s2LocalitySite_proved⟩

end SupercriticalLQGUniqueness.B2.Final
