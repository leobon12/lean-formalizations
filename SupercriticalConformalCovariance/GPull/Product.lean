import SupercriticalConformalCovariance.GPull.Measurable
import LQGMetric.Field.ExistGFF
import LQGMetric.Papers.DFGPS.L2_17Core2H
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory LQGMetric

namespace SupercriticalConformalCovariance.GPull

/-- An independent reference whole-plane GFF can be added without changing the original law. -/
theorem exists_reference_product {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    ∃ (P' : Measure (Ω × DistC)), IsProbabilityMeasure P' ∧
      MeasurePreserving (Prod.fst : Ω × DistC → Ω) P' P ∧
      IsWholePlaneGFF (fun p : Ω × DistC => p.2) P' ∧
      IndepFun (Prod.fst : Ω × DistC → Ω) Prod.snd P' := by
  obtain ⟨Ω₀, mΩ₀, P₀, g, hP₀, hg⟩ := GFFExist.exists_wholePlaneGFF
  let ν : Measure DistC := P₀.map g
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  let P' : Measure (Ω × DistC) := P.prod ν
  have hfst : MeasurePreserving (Prod.fst : Ω × DistC → Ω) P' P :=
    measurePreserving_fst
  have hsnd : MeasurePreserving (Prod.snd : Ω × DistC → DistC) P' ν :=
    measurePreserving_snd
  have hg' : IsWholePlaneGFF (fun p : Ω × DistC => p.2) P' := by
    apply DFGPS.L217.isWholePlaneGFF_of_map_eq measurable_snd hg
    exact hsnd.map_eq.trans rfl
  have hind : IndepFun (Prod.fst : Ω × DistC → Ω) Prod.snd P' := by
    apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable).2
    simpa only [P', hfst.map_eq, hsnd.map_eq] using
      (show P'.map (fun p : Ω × DistC => (p.1, p.2)) = P.prod ν by
        simpa [P'] using (Measure.map_id : P'.map id = P'))
  exact ⟨P', inferInstance, hfst, hg', hind⟩


end SupercriticalConformalCovariance.GPull
