import HigherDimLQGMetric.B3.Interfaces
import LQGMetric.Papers.LM.LocCI
import LQGMetric.Papers.DFGPS.L2_19CI

/-!
# Conditional-independence algebra for two local metric copies

The probability argument in MA5 A16 is separated from the metric-specific measurability
bookkeeping. All sigma-algebra inclusions are exact in this lemma.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric
open LQGMetric.DFGPS.L219
open LQGMetric.LM
open LQGMetric.GM.Bilip

namespace HigherDimLQGMetric

/-- If each inside observation is local relative to its own outside observation and the two
entire copies are conditionally independent given the field, the pair is jointly local. -/
theorem l7b_joint_ci {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {G H S₁ S₂ A₁ A₂ B₁ B₂ : MeasurableSpace Ω}
    (hG : G ≤ H) (hH : H ≤ mΩ) (hS₁ : S₁ ≤ mΩ) (hS₂ : S₂ ≤ mΩ)
    (hA₁ : A₁ ≤ mΩ) (hA₂ : A₂ ≤ mΩ) (hB₁ : B₁ ≤ mΩ) (hB₂ : B₂ ≤ mΩ)
    (hobs₁ : A₁ ⊔ B₁ ≤ S₁ ⊔ H) (hobs₂ : A₂ ⊔ B₂ ≤ S₂ ⊔ H)
    (hloc₁ : CondIndepEv G A₁ (H ⊔ B₁) P)
    (hloc₂ : CondIndepEv G A₂ (H ⊔ B₂) P)
    (hcopy : CondIndepEv H S₁ S₂ P) :
    CondIndepEv G (A₁ ⊔ A₂) (H ⊔ B₁ ⊔ B₂) P := by
  let B := H ⊔ B₁ ⊔ B₂
  have hGm : G ≤ mΩ := hG.trans hH
  have hBm : B ≤ mΩ := sup_le (sup_le hH hB₁) hB₂
  have hstep₁ : CondIndepEv (H ⊔ B₁) A₁ (A₂ ⊔ B₂) P := by
    apply CondIndepEv.symm
    refine condIndepEv_transfer hH hS₂ hS₁ (sup_le hH hB₁) hcopy.symm
      (le_sup_left.trans (le_aeClosure _)) ?_ ?_ ?_
    · exact (sup_le le_sup_right ((le_sup_right : B₁ ≤ A₁ ⊔ B₁).trans hobs₁)).trans
        (le_aeClosure _)
    · exact (hobs₂.trans (sup_le le_sup_left (le_sup_left.trans le_sup_right))).trans
        (le_aeClosure _)
    · exact (((le_sup_left : A₁ ≤ A₁ ⊔ B₁).trans hobs₁).trans
        (sup_le le_sup_left (le_sup_left.trans le_sup_right))).trans (le_aeClosure _)
  have hbig₁ : CondIndepEv G A₁ ((H ⊔ B₁) ⊔ (A₂ ⊔ B₂)) P :=
    condIndepEv_contraction hGm hA₁ (sup_le hH hB₁) (sup_le hA₂ hB₂)
      hloc₁ (by rwa [sup_eq_left.mpr (hG.trans le_sup_left)])
  have hstep₂ : CondIndepEv (H ⊔ B₂) A₂ B₁ P := by
    apply CondIndepEv.symm
    refine condIndepEv_transfer hH hS₁ hS₂ (sup_le hH hB₂) hcopy
      (le_sup_left.trans (le_aeClosure _)) ?_ ?_ ?_
    · exact (sup_le le_sup_right ((le_sup_right : B₂ ≤ A₂ ⊔ B₂).trans hobs₂)).trans
        (le_aeClosure _)
    · exact (((le_sup_right : B₁ ≤ A₁ ⊔ B₁).trans hobs₁).trans
        (sup_le le_sup_left (le_sup_left.trans le_sup_right))).trans (le_aeClosure _)
    · exact (((le_sup_left : A₂ ≤ A₂ ⊔ B₂).trans hobs₂).trans
        (sup_le le_sup_left (le_sup_left.trans le_sup_right))).trans (le_aeClosure _)
  have hbig₂ : CondIndepEv G A₂ ((H ⊔ B₂) ⊔ B₁) P :=
    condIndepEv_contraction hGm hA₂ (sup_le hH hB₂) hB₁ hloc₂
      (by rwa [sup_eq_left.mpr (hG.trans le_sup_left)])
  have hBcopy₁ : CondIndepEv G A₁ B P :=
    hbig₁.mono le_rfl (sup_le (sup_le
      (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left))
      (le_sup_right.trans le_sup_right))
  have hBcopy₂ : CondIndepEv G A₂ B P :=
    hbig₂.mono le_rfl (sup_le (sup_le
      (le_sup_left.trans le_sup_left) le_sup_right)
      (le_sup_right.trans le_sup_left))
  have hpair : CondIndepEv (B ⊔ G) A₁ A₂ P := by
    refine condIndepEv_transfer hGm hA₁ (sup_le (sup_le hH hB₁) (sup_le hA₂ hB₂))
      (sup_le hBm hGm) hbig₁
      (le_sup_right.trans (le_aeClosure _)) ?_ ?_ ?_
    · have hb : B ≤ ((H ⊔ B₁) ⊔ (A₂ ⊔ B₂)) ⊔ G := by
        dsimp [B]
        exact sup_le (le_sup_left.trans le_sup_left)
          ((le_sup_right.trans le_sup_right).trans le_sup_left)
      exact (sup_le hb le_sup_right).trans (le_aeClosure _)
    · exact le_sup_left.trans (le_aeClosure _)
    · exact (((le_sup_left : A₂ ≤ A₂ ⊔ B₂).trans le_sup_right).trans le_sup_left).trans
        (le_aeClosure _)
  exact (condIndepEv_sup_of_condIndepEv hGm hBm hA₁ hA₂ hBcopy₁.symm hBcopy₂.symm
    (by simpa [sup_assoc, sup_comm, sup_left_comm] using hpair)).symm

end HigherDimLQGMetric
