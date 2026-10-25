import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.CompactSetDist
import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.E5WitnessBorel




set_option autoImplicit false
noncomputable section
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents

abbrev SetGeoInput := LSCMetric × (Measurability.GeodesicCodes.Path × (ℂ × ℂ))

 


def SetGeoCandidate (K₁ K₂ : Set ℂ) (p : SetGeoInput) : Prop :=
  Measurability.GeodesicCodes.GeoCode p ∧ p.2.2.1 ∈ K₁ ∧ p.2.2.2 ∈ K₂ ∧
  p.1 (p.2.2.1, p.2.2.2) = OptimalConstants.Ratios.setDist p.1 K₁ K₂

attribute [local irreducible] SetGeoCandidate

theorem setGeoCandidate_measurable (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    MeasurableSet {p : SetGeoInput | SetGeoCandidate K₁ K₂ p} := by
  have hD : Measurable (fun p : SetGeoInput => p.1) := measurable_fst
  have hu : Measurable (fun p : SetGeoInput => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hv : Measurable (fun p : SetGeoInput => p.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hGeo : MeasurableSet {p : SetGeoInput | Measurability.GeodesicCodes.GeoCode p} :=
    Measurability.GeodesicCodes.geoCode_borel
  have hU : MeasurableSet {p : SetGeoInput | p.2.2.1 ∈ K₁} :=
    hK₁.isClosed.measurableSet.preimage hu
  have hV : MeasurableSet {p : SetGeoInput | p.2.2.2 ∈ K₂} :=
    hK₂.isClosed.measurableSet.preimage hv
  have hCost : Measurable (fun p : SetGeoInput => p.1 (p.2.2.1, p.2.2.2)) :=
    TwoScale.S36Events.jointEval_lsc.measurable.comp (hD.prodMk (hu.prodMk hv))
  have hDist : Measurable (fun p : SetGeoInput => OptimalConstants.Ratios.setDist p.1 K₁ K₂) :=
    (measurable_setDist_compact K₁ K₂ hK₁ hK₂).comp hD
  have hEq : MeasurableSet {p : SetGeoInput |
      p.1 (p.2.2.1, p.2.2.2) = OptimalConstants.Ratios.setDist p.1 K₁ K₂} :=
    measurableSet_eq_fun hCost hDist
  have hAll := ((hGeo.inter hU).inter hV).inter hEq
  convert hAll using 1
  ext p
  simp only [SetGeoCandidate, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

end SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents
