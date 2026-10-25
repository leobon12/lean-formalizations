import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.SetGeoUniqueBridge
import Mathlib.MeasureTheory.Constructions.Polish.Basic




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
open LQGMetric (DistC)

theorem uniqueSetGeoCandidateEvent_um
    (D : DistC → LSCMetric) (hD : Measurable D)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    LQGMetric.UMeasurableSet
      {g : DistC | ∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
        Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, w)} := by
  let W := Measurability.GeodesicCodes.Path × (ℂ × ℂ)
  have hStdWW : StandardBorelSpace (W × W) :=
    @StandardBorelSpace.prod W (inferInstance) W (inferInstance)
      (inferInstance) (inferInstance)
  let C : Set (LSCMetric × W) :=
    {p | Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ p}
  have hC : MeasurableSet C :=
    Measurability.ClauseEvents.setGeoCandidate_measurable K₁ K₂ hK₁ hK₂
  let B : Set (LSCMetric × (W × W)) :=
    {p | (p.1, p.2.1) ∈ C ∧ (p.1, p.2.2) ∈ C ∧ p.2.1 ≠ p.2.2}
  have hB : MeasurableSet B := by
    have hleft : Measurable (fun p : LSCMetric × (W × W) => (p.1, p.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hright : Measurable (fun p : LSCMetric × (W × W) => (p.1, p.2.2)) :=
      measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    have hneq : MeasurableSet
        {p : LSCMetric × (W × W) | p.2.1 ≠ p.2.2} :=
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
        (measurable_snd.comp measurable_snd)).compl
    have hparts := ((hC.preimage hleft).inter (hC.preimage hright)).inter hneq
    convert hparts using 1
    ext p
    simp only [B, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  have hExists : LQGMetric.UMeasurableSet
      {g : DistC | ∃ w : W, (D g, w) ∈ C} :=
    Measurability.GeodesicCodes.witnessProjection_um D hD hC
  have hBad : LQGMetric.UMeasurableSet
      {g : DistC | ∃ p : W × W, (D g, p) ∈ B} :=
    @Measurability.GeodesicCodes.witnessProjection_um (W × W) (inferInstance) hStdWW D hD B hB
  have hEq :
      {g : DistC | ∃! w : W, (D g, w) ∈ C} =
      {g : DistC | ∃ w : W, (D g, w) ∈ C} ∩
        {g : DistC | ∃ p : W × W, (D g, p) ∈ B}ᶜ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨w, hw, huniq⟩
      refine ⟨⟨w, hw⟩, ?_⟩
      rintro ⟨⟨w₁, w₂⟩, hw₁, hw₂, hne⟩
      exact hne ((huniq w₁ hw₁).trans (huniq w₂ hw₂).symm)
    · rintro ⟨⟨w, hw⟩, hnotBad⟩
      refine ⟨w, hw, ?_⟩
      intro w' hw'
      by_contra hne
      exact hnotBad ⟨(w, w'), hw, hw', Ne.symm hne⟩
  convert hExists.inter hBad.compl using 1
  exact hEq

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
