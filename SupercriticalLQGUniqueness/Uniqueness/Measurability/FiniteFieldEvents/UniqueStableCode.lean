import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.StableSourceBridge




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
open LQGMetric (DistC)

abbrev StableWitness := (Measurability.GeodesicCodes.Path × (ℂ × ℂ)) × (Fin 5 → ℝ)

def UniqueStableCodeField (Db Da : DistC → LSCMetric)
    (K₁ K₂ W : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (L : ℝ≥0∞) (g : DistC) : Prop :=
  (∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
    Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (Db g, w)) ∧
  ∃ w : StableWitness,
    Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (Db g, w.1) ∧
      StableCode W V L ((Da g, w.1.1), w.2)

theorem uniqueStableCodeField_um
    (Db Da : DistC → LSCMetric) (hDb : Measurable Db) (hDa : Measurable Da)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (W : Set ℂ) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (V : TopologicalSpace.Opens ℂ) (L : ℝ≥0∞) :
    LQGMetric.UMeasurableSet
      {g : DistC | UniqueStableCodeField Db Da K₁ K₂ W V L g} := by
  have hStd : StandardBorelSpace StableWitness :=
    @StandardBorelSpace.prod (Measurability.GeodesicCodes.Path × (ℂ × ℂ)) (inferInstance)
      (Fin 5 → ℝ) (inferInstance) (inferInstance) (inferInstance)
  let Rel : Set (DistC × StableWitness) :=
    {p | Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (Db p.1, p.2.1) ∧
      StableCode W V L ((Da p.1, p.2.1.1), p.2.2)}
  have hCandidateMap : Measurable (fun p : DistC × StableWitness =>
      (Db p.1, p.2.1)) :=
    (hDb.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have hStableMap : Measurable (fun p : DistC × StableWitness =>
      ((Da p.1, p.2.1.1), p.2.2)) :=
    ((hDa.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)
  have hRel : MeasurableSet Rel :=
    ((Measurability.ClauseEvents.setGeoCandidate_measurable K₁ K₂ hK₁ hK₂).preimage hCandidateMap).inter
      ((stableCode_borel hW hWc V L).preimage hStableMap)
  have hExist : LQGMetric.UMeasurableSet
      {g : DistC | ∃ w : StableWitness, (g, w) ∈ Rel} :=
    @LQGMetric.UMeasurableSet.setOf_exists DistC StableWitness
      (inferInstance) (inferInstance) (inferInstance) hStd Rel hRel
  have hUnique := Measurability.SetGeodesicCodes.uniqueSetGeoCandidateEvent_um Db hDb K₁ K₂ hK₁ hK₂
  convert hUnique.inter hExist using 1
  ext g
  rfl

theorem uniqueStableSource_iff_code
    (Db Da : LSCMetric)
    (hforgetb : Continuous (Measurability.SetGeodesicCodes.euclidForget Db))
    (hforgeta : Continuous (Measurability.SetGeodesicCodes.euclidForget Da))
    (K₁ K₂ W : Set ℂ) (hW : IsOpen W) (hWne : Wᶜ.Nonempty)
    (V : TopologicalSpace.Opens ℂ) (hVW : closure (V : Set ℂ) ⊆ W)
    (L : ℝ≥0∞) :
    (∃ P : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.UniqueSetGeodesic Db K₁ K₂ P T ∧
        SourceStable Da P T W V L) ↔
    ((∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (Db, w)) ∧
      ∃ w : StableWitness,
        Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (Db, w.1) ∧
          StableCode W V L ((Da, w.1.1), w.2)) := by
  constructor
  · rintro ⟨P, T, hUnique, hStable⟩
    rcases hStable with ⟨a, b, c, d, hex, hbW, hcW, hcost⟩
    have hT : 0 < T := excursion_total_time_pos P T W hW V hVW a b c d hex
    have hStable : SourceStable Da P T W V L :=
      ⟨a, b, c, d, hex, hbW, hcW, hcost⟩
    have hUniqueCode :=
      (Measurability.SetGeodesicCodes.uniqueSetGeodesic_iff_unique_candidate Db K₁ K₂ hforgetb).1
        ⟨P, T, hUnique⟩
    obtain ⟨R, hCandidate, hscaled⟩ :=
      Measurability.SetGeodesicCodes.setGeodesic_scaled_candidate Db K₁ K₂ P T hforgetb hUnique.1
    obtain ⟨q, hUnit, hCostCode⟩ :=
      (sourceStable_iff_codedStable_of_scaled Da hforgeta P T R hT hscaled
        W hW hWne V hVW L).1 hStable
    exact ⟨hUniqueCode, ((R, (P 0, P T)), q), hCandidate,
      hUnit, hCostCode⟩
  · rintro ⟨hUniqueCode, ⟨⟨R, ⟨u, v⟩⟩, q⟩, hCandidate, hUnit, hCostCode⟩
    obtain ⟨P', T', hUnique⟩ :=
      (Measurability.SetGeodesicCodes.uniqueSetGeodesic_iff_unique_candidate Db K₁ K₂ hforgetb).2
        hUniqueCode
    obtain ⟨P, T, hSet, hscaled'⟩ :=
      Measurability.SetGeodesicCodes.setGeoCandidate_has_scaled_source Db K₁ K₂ R u v hCandidate
    have hscaled : ∀ s : unitInterval, R s = P (T * (s : ℝ)) :=
      fun s => (hscaled' s).symm
    have hT : 0 < T := scaled_time_pos_of_unitExcursion P T R
      hSet.1.1.1 hscaled W hW V hVW q hUnit
    have hStableP : SourceStable Da P T W V L :=
      (sourceStable_iff_codedStable_of_scaled Da hforgeta P T R hT hscaled
        W hW hWne V hVW L).2 ⟨q, hUnit, hCostCode⟩
    obtain ⟨hTT', hEq⟩ := hUnique.2 P T hSet
    subst T
    exact ⟨P', T', hUnique,
      (sourceStable_congr_on Da P P' T' W V L hEq).1 hStableP⟩

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
