import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.FV2FamilyBudget
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.OptimalFinite




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem uniform_fixed_scale_raw_probability_budget
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q : ℝ)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (cMinus cPlus : ℝ≥0∞)
    (hstrict : cMinus < cPlus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) :
    ∃ Ccard : ℕ, 1 < Ccard ∧
      ∀ (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
        (_hK₁ : IsCompact K₁) (_hK₂ : IsCompact K₂)
        (obj : ∀ i : ℤ × ℤ,
          ObjectAtV2 P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) par pbar
            (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
        (k : ℕ),
        (∑' Z : Finset (ℤ × ℤ),
          P {ω | EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
            EndSaving.FiniteEvents.FV2 P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus)
              cPlus par pbar r b q K₁ K₂ obj Z (h ω)}) ≤
          ENNReal.ofReal ((max par.Crn 1) ^ k) * (Ccard ^ k : ℕ) := by
  have hcPtop := upper_optimal_constant_lt_top P h hh D D' ξ Q hD hD' cPlus hPlus
  have hcMtop : cMinus < ⊤ := hstrict.trans hcPtop
  have hmreal : cMinus.toReal < cPlus.toReal :=
    (ENNReal.toReal_lt_toReal hcMtop.ne hcPtop.ne).2 hstrict
  let cP : NNReal := cPlus.toNNReal
  have hcP : (cP : ℝ≥0∞) = cPlus := ENNReal.coe_toNNReal hcPtop.ne
  have hcPr : (cP : ℝ) = cPlus.toReal := rfl
  have hmid0 : 0 ≤ EndSaving.Interfaces.midpoint cMinus cPlus := by
    unfold EndSaving.Interfaces.midpoint
    have hM := ENNReal.toReal_nonneg (a := cMinus)
    have hP := ENNReal.toReal_nonneg (a := cPlus)
    positivity
  have hmid : EndSaving.Interfaces.midpoint cMinus cPlus < (cP : ℝ) := by
    rw [hcPr]
    unfold EndSaving.Interfaces.midpoint
    linarith only [hmreal]
  have hPlusP : ∀ᵐ ω ∂P,
      OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = (cP : ℝ≥0∞) := by
    simpa only [hcP] using hPlus
  obtain ⟨Ccard, hCcard, hcard⟩ := EndSaving.Counting.prop_card_ae
    P h hh D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) hD hD'
    cP hmid0 hmid hPlusP par pbar
  refine ⟨Ccard, hCcard, ?_⟩
  intro r b q K₁ K₂ hK₁ hK₂ obj k
  have hcardHere := hcard r b q K₁ K₂ obj k
  rw [hcP] at hcardHere
  exact fixed_scale_raw_probability_budget P h hh D D' ξ Q
    (EndSaving.Interfaces.midpoint cMinus cPlus) cPlus hD hD' par pbar
    r b q K₁ K₂ hK₁ hK₂ obj k Ccard hcardHere

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
