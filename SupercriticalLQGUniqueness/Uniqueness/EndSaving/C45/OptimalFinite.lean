import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.RNArithmetic
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.EBL




 
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
open LQGMetric (DistC)

 
theorem upper_optimal_constant_lt_top
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (cPlus : ℝ≥0∞)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) :
    cPlus < ⊤ := by
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D D' hD hD'
  have hfield : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.detGFFPlusCont hh.1
  have hboth := (hEBL P h hfield).and hPlus
  obtain ⟨ω, hω, hopt⟩ := hboth.exists
  have hupper : OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) ≤ ENNReal.ofReal K := by
    unfold OptimalConstants.Ratios.upperOptimal
    refine iSup_le fun z => iSup_le fun w => iSup_le fun hp => ?_
    exact (ENNReal.div_le_iff' hp.2.2.2.1.ne' hp.2.2.2.2.ne).2
      (by simpa only [mul_comm] using (hω z w).1)
  rw [hopt] at hupper
  exact hupper.trans_lt ENNReal.ofReal_lt_top

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
