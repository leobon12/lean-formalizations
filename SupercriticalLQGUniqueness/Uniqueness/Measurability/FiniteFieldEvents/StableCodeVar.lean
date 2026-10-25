import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.RawStableMeas




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
open LQGMetric (DistC)

theorem stableCode_joint_borel {W : Set ℂ} (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (V : TopologicalSpace.Opens ℂ) :
    MeasurableSet {p : ℝ≥0∞ × StableCodeInput |
      StableCode W V p.1 p.2} := by
  have hUnitInput : Measurable (fun p : ℝ≥0∞ × StableCodeInput =>
      (p.2.1.2, p.2.2)) :=
    ((measurable_snd.comp measurable_fst).comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd)
  have hScalarInput : Measurable (fun p : ℝ≥0∞ × StableCodeInput =>
      (p.2.1.1, (p.2.1.2, p.2.2))) :=
    ((measurable_fst.comp measurable_fst).comp measurable_snd).prodMk
      hUnitInput
  have hExc : MeasurableSet {p : ℝ≥0∞ × StableCodeInput |
      UnitExcursion W V (p.2.1.2, p.2.2)} :=
    (unitExcursion_borel W hW V).preimage hUnitInput
  have hCost : MeasurableSet {p : ℝ≥0∞ × StableCodeInput |
      p.1 ≤ excursionInternalProxy W (p.2.1.1, (p.2.1.2, p.2.2))} :=
    measurableSet_le measurable_fst
      ((excursionInternalProxy_measurable hWc).comp hScalarInput)
  exact hExc.inter hCost

def UniqueStableCodeFieldVar (Db Da : DistC → LSCMetric)
    (K₁ K₂ W : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (L : DistC → ℝ≥0∞) (g : DistC) : Prop :=
  (∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
    Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (Db g, w)) ∧
  ∃ w : StableWitness,
    Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (Db g, w.1) ∧
      StableCode W V (L g) ((Da g, w.1.1), w.2)

theorem uniqueStableCodeFieldVar_um
    (Db Da : DistC → LSCMetric) (hDb : Measurable Db) (hDa : Measurable Da)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (W : Set ℂ) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (V : TopologicalSpace.Opens ℂ) (L : DistC → ℝ≥0∞)
    (hL : Measurable L) :
    LQGMetric.UMeasurableSet
      {g : DistC | UniqueStableCodeFieldVar Db Da K₁ K₂ W V L g} := by
  have hStd : StandardBorelSpace StableWitness :=
    @StandardBorelSpace.prod (Measurability.GeodesicCodes.Path × (ℂ × ℂ)) (inferInstance)
      (Fin 5 → ℝ) (inferInstance) (inferInstance) (inferInstance)
  let Rel : Set (DistC × StableWitness) :=
    {p | Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (Db p.1, p.2.1) ∧
      StableCode W V (L p.1) ((Da p.1, p.2.1.1), p.2.2)}
  have hCandidateMap : Measurable (fun p : DistC × StableWitness =>
      (Db p.1, p.2.1)) :=
    (hDb.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have hStableMap : Measurable (fun p : DistC × StableWitness =>
      ((Da p.1, p.2.1.1), p.2.2)) :=
    ((hDa.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)
  have hJoint : Measurable (fun p : DistC × StableWitness =>
      (L p.1, ((Da p.1, p.2.1.1), p.2.2))) :=
    (hL.comp measurable_fst).prodMk hStableMap
  have hRel : MeasurableSet Rel :=
    ((Measurability.ClauseEvents.setGeoCandidate_measurable K₁ K₂ hK₁ hK₂).preimage hCandidateMap).inter
      ((stableCode_joint_borel hW hWc V).preimage hJoint)
  have hExist : LQGMetric.UMeasurableSet
      {g : DistC | ∃ w : StableWitness, (g, w) ∈ Rel} :=
    @LQGMetric.UMeasurableSet.setOf_exists DistC StableWitness
      (inferInstance) (inferInstance) (inferInstance) hStd Rel hRel
  have hUnique := Measurability.SetGeodesicCodes.uniqueSetGeoCandidateEvent_um Db hDb K₁ K₂ hK₁ hK₂
  convert hUnique.inter hExist using 1
  ext g
  rfl

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
