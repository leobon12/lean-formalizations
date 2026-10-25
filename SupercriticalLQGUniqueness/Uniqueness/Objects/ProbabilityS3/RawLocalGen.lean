import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.ScaleGood




 





set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem aeEventIn_regGood_open_of_barrier
    (P : Measure LQGMetric.DistC) [IsProbabilityMeasure P]
    (h : LQGMetric.DistC → LQGMetric.DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (hB : ∀ᵐ g ∂P, BiLipschitz.Barrier.Barrier (D (h g)))
    (C : Objects.CorrectedEvent.Constants) (w : ℂ) (s : ℝ) (hs : 0 < s)
    (U : TopologicalSpace.Opens ℂ)
    (hK : BiLipschitz.Barrier.closedAnn w s (2*s) ⊆ (U : Set ℂ))
    (hA : EuclideanAnnulus.toSet
      (⟨(w, s, 2*s), hs, by linarith⟩ : EuclideanAnnulus) ⊆ (U : Set ℂ)) :
    AEEventIn P (fieldSigma h U)
      {g | Objects.CorrectedEvent.regGood C (D (h g)) s w} := by
  let B : Set LQGMetric.DistC := {g | Objects.CorrectedEvent.regGood C (D (h g)) s w}
  obtain ⟨F, _, hLoc⟩ := hD.locality P h hh U
  have hLen := hD.length P h hh
  let Wraw : Set LQGMetric.DistC := {g | BiLipschitz.Barrier.Barrier (D (h g)) ∧
    (D (h g)).IsLengthSpace ∧ (D (h g)).internal (U : Set ℂ) =
      F (LQGMetric.restrictTo U (h g))}
  have hWraw : ∀ᵐ g ∂P, g ∈ Wraw := by
    filter_upwards [hB, hLen, hLoc] with g hb hl hf
    exact ⟨hb, hl, hf⟩
  obtain ⟨W, hWae, hWm, hWsub⟩ := hWraw.exists_measurable_mem
  let R : LQGMetric.DistC → (LQGMetric.CoordJ → ℝ) :=
    fun g => LQGMetric.pairJ U (LQGMetric.restrictTo U (h g))
  have hRm : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp
      ((LQGMetric.measurable_restrictTo U).comp hh.1)
  have hRfield : Measurable[fieldSigma h U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hSat : ∀ g₁ ∈ W, ∀ g₂ ∈ W,
      R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    intro g₁ hg₁ g₂ hg₂ hR hgood
    have hr : LQGMetric.restrictTo U (h g₁) = LQGMetric.restrictTo U (h g₂) :=
      LQGMetric.injective_pairJ U hR
    have hint : (D (h g₁)).internal (U : Set ℂ) =
        (D (h g₂)).internal (U : Set ℂ) := by
      calc
        _ = F (LQGMetric.restrictTo U (h g₁)) := (hWsub g₁ hg₁).2.2
        _ = F (LQGMetric.restrictTo U (h g₂)) := by rw [hr]
        _ = _ := ((hWsub g₂ hg₂).2.2).symm
    exact (regGood_iff_of_internal_eq C (D (h g₁)) (D (h g₂))
      (hWsub g₁ hg₁).1 (hWsub g₂ hg₂).1
      (hWsub g₁ hg₁).2.1 (hWsub g₂ hg₂).2.1 w s hs U
      hK hA hint).mp hgood
  have hBm : NullMeasurableSet B P :=
    ((Objects.ClauseMeasurability.measurableSet_regGood C D hD.measurable s hs w).preimage hh.1).nullMeasurableSet
  exact LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := B) (W := W)
    measurable_id hRm hRfield (Filter.Eventually.of_forall fun _ => rfl)
    hWm (by simpa only [Measure.map_id] using hBm) hWae hSat

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
