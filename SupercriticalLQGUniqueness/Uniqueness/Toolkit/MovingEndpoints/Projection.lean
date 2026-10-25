import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.Witness
import LQGMetric.Meas.UM
import LQGMetric.Field.StandardBorelRange




 


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open LQGMetric (DistC)
namespace SupercriticalLQGUniqueness
namespace Uniqueness.Toolkit.MovingEndpoints

 

theorem GWitnessEvent_um (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E) (r κ C : ℝ) :
    LQGMetric.UMeasurableSet
      {h : DistC | ∃ z w : ℂ, GWitness r κ C ((D h, E h), (z, w))} := by
  letI : SecondCountableTopology LSCMetric :=
    LSCMetric.isInducing_toLSCFun.secondCountableTopology
  have hrel : MeasurableSet {p : WitnessCarrier | GWitness r κ C p} := by
    have hEq : (Prod.instMeasurableSpace : MeasurableSpace WitnessCarrier) = borel WitnessCarrier :=
      BorelSpace.measurable_eq
    exact hEq.symm ▸ GWitness_borel r κ C
  have hlift : Measurable (fun p : DistC × (ℂ × ℂ) =>
      (((D p.1, E p.1), p.2) : WitnessCarrier)) := by
    fun_prop
  have hset : MeasurableSet {p : DistC × (ℂ × ℂ) |
      GWitness r κ C ((D p.1, E p.1), p.2)} := hrel.preimage hlift
  have hum := LQGMetric.UMeasurableSet.setOf_exists hset
  convert hum using 1
  ext h
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, w, hzw⟩
    exact ⟨(z, w), hzw⟩
  · rintro ⟨⟨z, w⟩, hzw⟩
    exact ⟨z, w, hzw⟩

 

theorem witnessProjection_um (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E)
    {S : Set WitnessCarrier}
    (hS : @MeasurableSet WitnessCarrier (borel _) S) :
    LQGMetric.UMeasurableSet
      {h : DistC | ∃ z w : ℂ, ((D h, E h), (z, w)) ∈ S} := by
  letI : SecondCountableTopology LSCMetric :=
    LSCMetric.isInducing_toLSCFun.secondCountableTopology
  have hrel : MeasurableSet S := by
    have hEq : (Prod.instMeasurableSpace : MeasurableSpace WitnessCarrier) =
        borel WitnessCarrier := BorelSpace.measurable_eq
    exact hEq.symm ▸ hS
  have hlift : Measurable (fun p : DistC × (ℂ × ℂ) =>
      (((D p.1, E p.1), p.2) : WitnessCarrier)) := by
    fun_prop
  have hset : MeasurableSet {p : DistC × (ℂ × ℂ) |
      (((D p.1, E p.1), p.2) : WitnessCarrier) ∈ S} := hrel.preimage hlift
  have hum := LQGMetric.UMeasurableSet.setOf_exists hset
  convert hum using 1
  ext h
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, w, hzw⟩
    exact ⟨(z, w), hzw⟩
  · rintro ⟨⟨z, w⟩, hzw⟩
    exact ⟨z, w, hzw⟩

 

theorem GtildeWitnessEvent_um (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E) (r κ C : ℝ) :
    LQGMetric.UMeasurableSet
      {h : DistC | ∃ z w : ℂ, GtildeWitness r κ C ((D h, E h), (z, w))} :=
  witnessProjection_um D E hD hE (GtildeWitness_borel r κ C)

 

theorem LocalWitnessEvent_um (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E)
    (a : ENNReal) (z : ℂ) (r : ℝ) :
    LQGMetric.UMeasurableSet
      {h : DistC | ∃ u v : ℂ, LocalWitnessRelation a z r ((D h, E h), (u, v))} :=
  witnessProjection_um D E hD hE (LocalWitnessRelation_borel a z r)


end Uniqueness.Toolkit.MovingEndpoints
end SupercriticalLQGUniqueness
