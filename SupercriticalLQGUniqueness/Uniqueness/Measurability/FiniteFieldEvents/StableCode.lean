import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.ExcursionScalar




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

abbrev StableCodeInput := (LSCMetric × Measurability.GeodesicCodes.Path) × (Fin 5 → ℝ)

def StableCode (W : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (L : ℝ≥0∞) (p : StableCodeInput) : Prop :=
  UnitExcursion W V (p.1.2, p.2) ∧
    L ≤ excursionInternalProxy W (p.1.1, (p.1.2, p.2))

theorem stableCode_borel {W : Set ℂ} (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (V : TopologicalSpace.Opens ℂ)
    (L : ℝ≥0∞) :
    MeasurableSet {p : StableCodeInput | StableCode W V L p} := by
  have hinput : Measurable (fun p : StableCodeInput => (p.1.2, p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hscalar : Measurable (fun p : StableCodeInput =>
      (p.1.1, (p.1.2, p.2))) :=
    (measurable_fst.comp measurable_fst).prodMk hinput
  have hExc : MeasurableSet {p : StableCodeInput |
      UnitExcursion W V (p.1.2, p.2)} :=
    (unitExcursion_borel W hW V).preimage hinput
  have hCost : MeasurableSet {p : StableCodeInput |
      L ≤ excursionInternalProxy W (p.1.1, (p.1.2, p.2))} :=
    measurableSet_le measurable_const
      ((excursionInternalProxy_measurable hWc).comp hscalar)
  exact hExc.inter hCost

def CodedStable (W : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (L : ℝ≥0∞) (p : LSCMetric × Measurability.GeodesicCodes.Path) : Prop :=
  ∃ q : Fin 5 → ℝ, StableCode W V L (p, q)

theorem codedStable_field_um
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    {W : Set ℂ} (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (V : TopologicalSpace.Opens ℂ)
    (L : ℝ≥0∞) :
    LQGMetric.UMeasurableSet
      {g : LQGMetric.DistC |
        ∃ w : Measurability.GeodesicCodes.Path × (Fin 5 → ℝ),
          StableCode W V L ((D g, w.1), w.2)} := by
  have hmap : Measurable (fun p : LQGMetric.DistC ×
      (Measurability.GeodesicCodes.Path × (Fin 5 → ℝ)) => ((D p.1, p.2.1), p.2.2)) :=
    ((hD.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  exact LQGMetric.UMeasurableSet.setOf_exists
    ((stableCode_borel hW hWc V L).preimage hmap)

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
