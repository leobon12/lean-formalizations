import SupercriticalLQGUniqueness.B2.PfeLocal.AnnulusLocal
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.IntCode
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Papers.LM.L3_1N2P3
import LQGMetric.Field.GermSplitA

 







set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric (CondIndepEv)
open LQGMetric (DistC circleAvg addConst)

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric.Blueprint LQGMetric.GM.Bilip LQGMetric.DFGPS.L219

 


def lscInternalFam {Ω : Type*} (D : Ω → LSCMetric) :
    Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞ :=
  fun ω V u v => Uniqueness.TwoScale.S36.intExt (D ω) V u v

 


def lscNormIntFam {Ω : Type*} (ξ : ℝ) (h : Ω → DistC)
    (D : Ω → LSCMetric) (z : ℂ) (r : ℝ) :
    Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞ :=
  fun ω V u v =>
    ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) r z)) *
      lscInternalFam D ω V u v

namespace Inputs

 




def LscInternalMeasurable {Ω : Type} [MeasurableSpace Ω]
    (D : Ω → LSCMetric) : Prop :=
  ∀ V : TopologicalSpace.Opens ℂ, Measurable (fun ω => lscInternalFam D ω (V : Set ℂ))

 





def LscXiAdditiveLocality {Ω : Type} [MeasurableSpace Ω]
    (ξ : ℝ) (P : Measure Ω) (h : Ω → DistC) (D : Ω → LSCMetric) : Prop :=
  LQGMetric.Blueprint.IsJointlyLocalFam P h (lscInternalFam D) (lscInternalFam D) ∧
    ∀ (z : ℂ) (r : ℝ), 0 < r →
      LQGMetric.Blueprint.IsJointlyLocalFam P
        (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
        (lscNormIntFam ξ h D z r) (lscNormIntFam ξ h D z r)

end Inputs

 



theorem lscNormIntFam_measurable_of_inputs {Ω : Type} [MeasurableSpace Ω]
    {h : Ω → DistC} {D : Ω → LSCMetric}
    (hh : Measurable h) (hM : Inputs.LscInternalMeasurable D)
    (ξ : ℝ) (z : ℂ) (r : ℝ) (V : TopologicalSpace.Opens ℂ) :
    Measurable (fun ω => lscNormIntFam ξ h D z r ω (V : Set ℂ)) := by
  have hca : Measurable (fun ω => circleAvg (h ω) r z) :=
    (LQGMetric.measurable_circleAvg_left r z).comp hh
  have hfac : Measurable (fun ω =>
      ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) r z))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (hca.const_mul (-ξ)))
  have hI := hM V
  exact measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
    hfac.mul ((measurable_pi_apply v).comp
      ((measurable_pi_apply u).comp hI))

theorem lscNormIntFam_sigma_le_of_inputs {Ω : Type} [MeasurableSpace Ω]
    {h : Ω → DistC} {D : Ω → LSCMetric}
    (hh : Measurable h) (hM : Inputs.LscInternalMeasurable D)
    (ξ : ℝ) (z : ℂ) (r : ℝ) (V : TopologicalSpace.Opens ℂ) :
    LQGMetric.Blueprint.famSigma (lscNormIntFam ξ h D z r) V ≤
      ‹MeasurableSpace Ω› :=
  (lscNormIntFam_measurable_of_inputs hh hM ξ z r V).comap_le

 




theorem lsc_condIndep_scale_of_inputs {Ω : Type} [MeasurableSpace Ω]
    {ξ : ℝ} {P : Measure Ω} {h : Ω → DistC} {D : Ω → LSCMetric}
    (hX : Inputs.LscXiAdditiveLocality ξ P h D)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (V : TopologicalSpace.Opens ℂ) :
    CondIndepEv
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) V)
      (LQGMetric.Blueprint.famSigma (lscNormIntFam ξ h D z r) V)
      (LQGMetric.Blueprint.fieldSigmaClosed
          (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) (V : Set ℂ)ᶜ ⊔
        LQGMetric.Blueprint.famSigma (lscNormIntFam ξ h D z r)
          (closure (V : Set ℂ))ᶜ) P := by
  simpa only [sup_idem, sup_assoc] using hX.2 z r hr V

 





theorem lsc_condIndep_scale_field_of_inputs {Ω : Type} [mΩ : MeasurableSpace Ω]
    {ξ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} {D : Ω → LSCMetric}
    (hh : LQGMetric.IsNormalizedWPGFF h P)
    (hX : Inputs.LscXiAdditiveLocality ξ P h D)
    (hM : Inputs.LscInternalMeasurable D)
    {r : ℝ} (hr : 0 < r) (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ)) :
    CondIndepEv
      (LQGMetric.Blueprint.fieldSigma (LQGMetric.LM.recentre h r) V)
      (LQGMetric.Blueprint.famSigma (lscNormIntFam ξ h D 0 r) V)
      (MeasurableSpace.comap h inferInstance ⊔
        LQGMetric.Blueprint.famSigma (lscNormIntFam ξ h D 0 r)
          (closure (V : Set ℂ))ᶜ) P := by
  have J := lsc_condIndep_scale_of_inputs hX 0 r hr V
  have hXm : Measurable (LQGMetric.LM.recentre h r) :=
    LQGMetric.LM.measurable_recentre hh.1.measurable r
  have hXg : LQGMetric.IsWholePlaneGFF (LQGMetric.LM.recentre h r) P :=
    hh.1.addConst ((LQGMetric.measurable_circleAvg_left r 0).comp hh.1.measurable).neg
  have hG : fieldSigma (LQGMetric.LM.recentre h r) V ≤ mΩ :=
    ((LQGMetric.measurable_restrictTo V).comp hXm).comap_le
  have hS : ∀ W : TopologicalSpace.Opens ℂ,
      famSigma (lscNormIntFam ξ h D 0 r) W ≤ mΩ :=
    lscNormIntFam_sigma_le_of_inputs hh.1.measurable hM ξ 0 r
  have hWo : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have hOut : famSigma (lscNormIntFam ξ h D 0 r)
      (closure (V : Set ℂ))ᶜ ≤ mΩ := hS ⟨_, hWo⟩
  change CondIndepEv (fieldSigma (LQGMetric.LM.recentre h r) V)
    (famSigma (lscNormIntFam ξ h D 0 r) V)
    (fieldSigmaClosed (LQGMetric.LM.recentre h r) (V : Set ℂ)ᶜ ⊔
      famSigma (lscNormIntFam ξ h D 0 r) (closure (V : Set ℂ))ᶜ) P at J
  refine LQGMetric.DFGPS.L219.condIndepEv_transfer hG (hS V)
    (sup_le (LQGMetric.GM.fieldSigmaClosed_le_gm hXm _) hOut)
    hG J (le_aeClosure _) (le_sup_right.trans (le_aeClosure _))
    (le_sup_left.trans (le_aeClosure _)) (sup_le ?_
      ((le_sup_right.trans le_sup_left).trans (le_aeClosure _)))
  refine LQGMetric.LM.le_aeClosure_trans
    (LQGMetric.LM.comap_h_le_recentre hh r)
    ((LQGMetric.GermSplit.locGermSplitBdd P _ hXg V hVb).trans ?_)
  exact aeClosure_mono
    (sup_le le_sup_right (le_sup_left.trans le_sup_left))

end SupercriticalLQGUniqueness.B2.PfeLocal
