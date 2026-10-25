import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.SourceStatementsV2




 





















set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs

open LQGMetric (DistC)

 




def S36UpperInput : Prop :=
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
    ∀ (D D' : DistC → LSCMetric),
      IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ cPlus : ℝ≥0∞, 0 < cPlus → cPlus < ⊤ →
      (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
      ∃ θ : Set.Ioi (0 : ℝ),
      ∃ a : Set.Ioo (3 / 4 : ℝ) 1,
        ∃ p : Set.Ioo (0 : ℝ) 1,
          ∀ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
            ∃ n₁ : ℕ, ∀ n ≥ n₁,
              3 * n ≤ 4 * (EndSaving.Interfaces.upperGood P h D D' ξ Q a θ
                ⟨Ctop, Ctop.property.1⟩ p n).card

 



def S36LowerInput : Prop :=
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
    ∀ (D D' : DistC → LSCMetric),
      IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ cMinus : ℝ≥0∞, 0 < cMinus → cMinus < ⊤ →
      (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
      ∀ Cmid : {x : ℝ // cMinus.toReal < x},
        ∃ κ : Set.Ioi (0 : ℝ), ∃ n₂ : ℕ, ∀ n ≥ n₂,
          3 * n ≤ 4 * (EndSaving.Interfaces.lowerGood P h D D' κ
            ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ n).card

 
def S36Input : Prop := S36UpperInput ∧ S36LowerInput

 



def T58Input : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus),
    EndSaving.InterfaceV2.T58Statement P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict

 


def C45Input : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1) (R : EndSaving.Interfaces.AdmissibleRadii) (params : EndSaving.Interfaces.Parameters ξ)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) params pbar z r),
    EndSaving.InterfaceV2.C45CorrectedNonemptyInternal P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar R params family

end SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs
