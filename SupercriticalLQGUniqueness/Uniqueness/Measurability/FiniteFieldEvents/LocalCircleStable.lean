import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.RawStableVarMeas
import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.CircleValue




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
open LQGMetric (DistC TestC)

def localTimeThreshold (ξ Q Ctime : ℝ) (r : Set.Ioi (0 : ℝ))
    (z : ℂ) (g : DistC) : ℝ≥0∞ :=
  ENNReal.ofReal Ctime *
    ENNReal.ofReal ((r : ℝ) ^ (ξ * Q) *
      Real.exp (ξ * Measurability.ClauseEvents.circleValue r z g))

theorem localTimeThreshold_measurable (ξ Q Ctime : ℝ)
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    Measurable (localTimeThreshold ξ Q Ctime r z) := by
  have havg := Measurability.ClauseEvents.circleValue_measurable r z
  have hreal : Measurable (fun g : DistC =>
      ((r : ℝ) ^ (ξ * Q)) * Real.exp (ξ * Measurability.ClauseEvents.circleValue r z g)) :=
    measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul havg))
  exact measurable_const.mul (ENNReal.measurable_ofReal.comp hreal)

theorem sourceStable_circleAverage_iff
    (D : LSCMetric) (P : ℝ → ℂ) (T : ℝ)
    (W : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (ξ Q Ctime : ℝ) (r : Set.Ioi (0 : ℝ)) (z : ℂ)
    (g : DistC) :
    (∃ c : ℝ, IsCircleAverage g r z c ∧
      SourceStable D P T W V
        (ENNReal.ofReal Ctime * ENNReal.ofReal
          ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)))) ↔
    IsCircleAverage g r z (Measurability.ClauseEvents.circleValue r z g) ∧
      SourceStable D P T W V (localTimeThreshold ξ Q Ctime r z g) := by
  constructor
  · rintro ⟨c, hc, hstable⟩
    have hEq := Measurability.ClauseEvents.circleValue_eq_of_IsCircleAverage r z g c hc
    dsimp [localTimeThreshold]
    rw [hEq]
    exact ⟨hc, hstable⟩
  · rintro ⟨hc, hstable⟩
    exact ⟨Measurability.ClauseEvents.circleValue r z g, hc, hstable⟩

theorem rawUniqueStable_circle_shifted_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (W : Set ℂ) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWne : Wᶜ.Nonempty)
    (V : TopologicalSpace.Opens ℂ) (hVW : closure (V : Set ℂ) ⊆ W)
    (Ctime Q : ℝ) (r : Set.Ioi (0 : ℝ)) (z : ℂ) (φ : TestC) :
    NullMeasurableSet
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T ∧
        ∃ c : ℝ, IsCircleAverage g r z c ∧
          SourceStable (D g) P' T W V
            (ENNReal.ofReal Ctime * ENNReal.ofReal
              ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c)))}
      (P.map h) := by
  let L := localTimeThreshold (ξ : ℝ) Q Ctime r z
  have hL : Measurable L := localTimeThreshold_measurable (ξ : ℝ) Q Ctime r z
  let E : Set DistC :=
    {g | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.UniqueSetGeodesic
        (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T ∧
      SourceStable (D g) P' T W V (L g)}
  have hE : NullMeasurableSet E (P.map h) :=
    rawUniqueStable_var_shifted_nullMeasurable P h hh hD K₁ K₂ hK₁ hK₂
      W hW hWc hWne V hVW L hL φ
  let A : Set DistC :=
    {g | IsCircleAverage g r z (Measurability.ClauseEvents.circleValue r z g)}
  have hA : MeasurableSet A := Measurability.ClauseEvents.circleValue_graph_measurable r z
  have hEq :
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T ∧
        ∃ c : ℝ, IsCircleAverage g r z c ∧
          SourceStable (D g) P' T W V
            (ENNReal.ofReal Ctime * ENNReal.ofReal
              ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c)))} = A ∩ E := by
    ext g
    constructor
    · rintro ⟨P', T, hU, c, hc, hStable⟩
      obtain ⟨hAvg, hStable'⟩ :=
        (sourceStable_circleAverage_iff (D g) P' T W V
          (ξ : ℝ) Q Ctime r z g).1 ⟨c, hc, hStable⟩
      exact ⟨hAvg, P', T, hU, hStable'⟩
    · rintro ⟨hAvg, P', T, hU, hStable⟩
      obtain ⟨c, hc, hStable'⟩ :=
        (sourceStable_circleAverage_iff (D g) P' T W V
          (ξ : ℝ) Q Ctime r z g).2 ⟨hAvg, hStable⟩
      exact ⟨P', T, hU, c, hc, hStable'⟩
  rw [hEq]
  exact hA.nullMeasurableSet.inter hE

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
