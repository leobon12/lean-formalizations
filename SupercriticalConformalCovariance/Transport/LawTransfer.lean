import SupercriticalConformalCovariance.Transport.FactorCriterion
import LQGMetric.Papers.DFGPS.L2_17Core2H

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace
open LQGMetric (DistC DistOn IsWholePlaneGFF IsGFFPlusCont restrictTo ofCont)
open SupercriticalConformalCovariance (IsDomainRealization)

namespace SupercriticalConformalCovariance.Transport

abbrev RealizationData (V : Opens ℂ) :=
  DistOn V × (DistC × (C(V, ℝ) × C(ℂ, ℝ)))

private theorem measurable_wp (V : Opens ℂ) :
    Measurable (fun t : RealizationData V => t.2.1 - ofCont t.2.2.2) := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  simp only [ContinuousLinearMap.sub_apply]
  have h₁ : Measurable (fun t : RealizationData V => t.2.1 φ) :=
    (LQGMetric.measurable_distOn_apply φ).comp (measurable_fst.comp measurable_snd)
  have h₂ : Measurable (fun t : RealizationData V => (ofCont t.2.2.2) φ) :=
    (LQGMetric.measurable_ofCont_apply φ).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  convert h₁.sub h₂ using 1 <;> ext t <;> rfl

private theorem measurable_relation (V : Opens ℂ) :
    MeasurableSet {t : RealizationData V | t.1 = restrictTo V t.2.1 +
      Distribution.ofFun V (Function.extend Subtype.val t.2.2.1 0) volume ⊤} := by
  apply measurableSet_eq_fun measurable_fst
  have hm₀ : Measurable (fun t : RealizationData V => restrictTo V t.2.1) :=
    (LQGMetric.measurable_restrictTo V).comp (measurable_fst.comp measurable_snd)
  have hm₁ : Measurable (fun t : RealizationData V =>
      Distribution.ofFun V (Function.extend Subtype.val t.2.2.1 0) volume ⊤) :=
    (SupercriticalConformalCovariance.Domain.measurable_ofFun_extZ V)
      ((measurable_fst.comp measurable_snd).comp measurable_snd)
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  simp only [ContinuousLinearMap.add_apply]
  convert ((LQGMetric.measurable_distOn_apply φ).comp hm₀).add
    ((LQGMetric.measurable_distOn_apply φ).comp hm₁) using 1 <;> ext t <;> rfl

/-- Domain-realization hypotheses transfer along equality of the full joint law, including
one continuous witness for the whole-plane GFF-plus-continuous component. -/
theorem realization_of_joint_law_eq (V : Opens ℂ)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (J : Ω → RealizationData V) (J' : Ω' → RealizationData V)
    (hJ : Measurable J) (hJ' : Measurable J')
    (hR : IsDomainRealization V P (fun ω => (J ω).1)
      (fun ω => (J ω).2.1) (fun ω => (J ω).2.2.1))
    (hw : IsWholePlaneGFF (fun ω => (J ω).2.1 - ofCont (J ω).2.2.2) P)
    (hlaw : P'.map J' = P.map J) :
    IsDomainRealization V P' (fun ω => (J' ω).1)
      (fun ω => (J' ω).2.1) (fun ω => (J' ω).2.2.1) := by
  let T : RealizationData V → DistC := fun t => t.2.1 - ofCont t.2.2.2
  have hT : Measurable T := measurable_wp V
  have hwpLaw : P'.map (T ∘ J') = P.map (T ∘ J) := by
    rw [← Measure.map_map hT hJ', hlaw, Measure.map_map hT hJ]
  have hwp : IsWholePlaneGFF
      (fun ω => (J' ω).2.1 - ofCont (J' ω).2.2.2) P' := by
    apply LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq
      ((measurable_wp V).comp hJ') hw
    exact hwpLaw
  refine ⟨measurable_fst.comp hJ', ?_,
    ((measurable_fst.comp measurable_snd).comp measurable_snd).comp hJ', ?_⟩
  · refine ⟨(measurable_fst.comp measurable_snd).comp hJ',
      (fun ω => (J' ω).2.2.2),
      ((measurable_snd.comp measurable_snd).comp measurable_snd).comp hJ', ?_⟩
    exact hwp
  · have hrel := hR.2.2.2
    have hevent : ∀ᵐ t ∂(P.map J), t ∈ {t : RealizationData V |
        t.1 = restrictTo V t.2.1 +
          Distribution.ofFun V (Function.extend Subtype.val t.2.2.1 0) volume ⊤} := by
      apply (ae_map_iff hJ.aemeasurable (measurable_relation V)).2
      simpa only [Set.mem_setOf_eq] using hrel
    have hevent' : ∀ᵐ ω ∂P', J' ω ∈ {t : RealizationData V |
        t.1 = restrictTo V t.2.1 +
          Distribution.ofFun V (Function.extend Subtype.val t.2.2.1 0) volume ⊤} :=
      (ae_map_iff hJ'.aemeasurable (measurable_relation V)).1 (hlaw ▸ hevent)
    simpa only [Set.mem_setOf_eq] using hevent'

end SupercriticalConformalCovariance.Transport
