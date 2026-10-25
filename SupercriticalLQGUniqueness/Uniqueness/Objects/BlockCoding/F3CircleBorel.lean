import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness.BlockCircleBorel
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.JointEval




 





set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

abbrev F3Input (c : ℂ) (R : NNReal) :=
  (LSCMetric × LSCMetric) × ((closedBall c (R : ℝ)) × ℂ)

def f3Circle (c : ℂ) (R : NNReal) (lam : ℝ) (p : F3Input c R) : ENNReal :=
  Objects.Shadow.circleOuter c R 0
    (sphere c (R : ℝ) \
      Objects.Producer.goodSet p.1.1 c p.2.1 (R : ℝ)
        (lam * (p.1.2 ((p.2.1 : ℂ), p.2.2)).toReal)
        p.2.1.property)

 

theorem measurable_f3_circle (c : ℂ) (R : NNReal) (lam : ℝ) :
    Measurable (f3Circle c R lam) := by
  have hd : Measurable (fun p : F3Input c R => p.1.1) :=
    measurable_fst.comp measurable_fst
  have he : Measurable (fun p : F3Input c R => p.1.2) :=
    measurable_snd.comp measurable_fst
  have hu : Measurable (fun p : F3Input c R => (p.2.1 : ℂ)) := by
    fun_prop
  have hv : Measurable (fun p : F3Input c R => p.2.2) := by
    fun_prop
  have hEval : Measurable (fun p : F3Input c R =>
      p.1.2 ((p.2.1 : ℂ), p.2.2)) :=
    TwoScale.S36Events.jointEval_lsc.measurable.comp (he.prodMk (hu.prodMk hv))
  have hth : Measurable (fun p : F3Input c R =>
      lam * (p.1.2 ((p.2.1 : ℂ), p.2.2)).toReal) :=
    measurable_const.mul (ENNReal.measurable_toReal.comp hEval)
  have hbase := (Objects.BlockWitness.measurable_circle_bad c R).comp
    (hd.prodMk ((by fun_prop : Measurable
      (fun p : F3Input c R => p.2.1)).prodMk hth))
  exact hbase

abbrev F3PairInput (cU cV : ℂ) (RU RV : NNReal) :=
  (LSCMetric × LSCMetric) ×
    ((closedBall cU (RU : ℝ)) × (closedBall cV (RV : ℝ)))

def f3PairRelation (cU cV : ℂ) (RU RV : NNReal)
    (lam budgetU budgetV : ℝ) (p : F3PairInput cU cV RU RV) : Prop :=
  f3Circle cU RU lam (Prod.mk p.1 (Prod.mk p.2.1 (p.2.2 : ℂ))) ≤ ENNReal.ofReal budgetU ∧
  f3Circle cV RV lam (Prod.mk p.1 (Prod.mk p.2.2 (p.2.1 : ℂ))) ≤ ENNReal.ofReal budgetV

 

theorem measurableSet_f3PairRelation (cU cV : ℂ) (RU RV : NNReal)
    (lam budgetU budgetV : ℝ) :
    MeasurableSet {p : F3PairInput cU cV RU RV |
      f3PairRelation cU cV RU RV lam budgetU budgetV p} := by
  have hU : Measurable (fun p : F3PairInput cU cV RU RV =>
      (Prod.mk p.1 (Prod.mk p.2.1 (p.2.2 : ℂ)) : F3Input cU RU)) := by
    fun_prop
  have hV : Measurable (fun p : F3PairInput cU cV RU RV =>
      (Prod.mk p.1 (Prod.mk p.2.2 (p.2.1 : ℂ)) : F3Input cV RV)) := by
    fun_prop
  exact (measurableSet_le ((measurable_f3_circle cU RU lam).comp hU)
    measurable_const).inter
      (measurableSet_le ((measurable_f3_circle cV RV lam).comp hV)
        measurable_const)

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
