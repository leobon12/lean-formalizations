import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2.Bridges
import SLUMetricAPI2




 



set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability

theorem acr_eq_compactPathInf (D : LSCMetric) (w : ℂ) (a b : ℝ) :
    Objects.CorrectedEvent.acr D w a b =
      Toolkit.CompactPathInfimum.compactPathInf D (Objects.CorrectedEvent.cann w a b) (sphere w a) (sphere w b) := by
  unfold Objects.CorrectedEvent.acr Toolkit.CompactPathInfimum.compactPathInf
  apply iInf_congr; intro P
  apply iInf_congr; intro t
  apply iInf_congr; intro u
  apply iInf_congr; intro hP
  have hiff : (P '' Icc t u ⊆ Objects.CorrectedEvent.cann w a b) ↔
      ∀ v ∈ Icc t u, P v ∈ Objects.CorrectedEvent.cann w a b := by
    constructor
    · intro h v hv
      exact h ⟨v, hv, rfl⟩
    · intro h v hv
      obtain ⟨x, hx, rfl⟩ := hv
      exact h x hx
  rw [propext hiff]

private theorem isCompact_cann (w : ℂ) (a b : ℝ) :
    IsCompact (Objects.CorrectedEvent.cann w a b) := by
  have heq : Objects.CorrectedEvent.cann w a b = closedBall w b ∩ (ball w a)ᶜ := by
    ext x
    simp only [Objects.CorrectedEvent.cann, mem_ofPred_eq, mem_inter_iff, mem_closedBall,
      mem_compl_iff, mem_ball, not_lt]
    tauto
  rw [heq]
  exact (isCompact_closedBall w b).inter_right isOpen_ball.isClosed_compl

theorem measurable_acr (w : ℂ) (a b : ℝ) :
    Measurable (fun D : LSCMetric => Objects.CorrectedEvent.acr D w a b) := by
  have h := Toolkit.CompactPathInfimum.compactPathInf_measurable (isCompact_cann w a b)
    (isCompact_sphere w a) (isCompact_sphere w b)
  simpa only [← acr_eq_compactPathInf] using h

theorem around_eq_aroundDist (D : LSCMetric) (w : ℂ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    Objects.CorrectedEvent.around D w a b =
      aroundDist D (⟨(w, a, b), ha, hab⟩ : EuclideanAnnulus) := by
  let A : EuclideanAnnulus := ⟨(w, a, b), ha, hab⟩
  apply le_antisymm (Objects.ProbabilityS1S2.around_le_aroundDist D w a b ha hab)
  change aroundDist D A ≤ Objects.CorrectedEvent.around D w a b
  unfold Objects.CorrectedEvent.around
  refine le_iInf fun P => le_iInf fun t => le_iInf fun u =>
    le_iInf fun hcurve => le_iInf fun htrace => le_iInf fun hsep => ?_
  have htrace' : ∀ v ∈ Icc t u, P v ∈ A.toSet := by
    intro v hv
    have hm : P v ∈ Objects.CorrectedEvent.ann w a b := htrace ⟨v, hv, rfl⟩
    change P v ∈ ball w b \ closure (ball w a)
    rw [closure_ball _ ha.ne']
    simpa only [Objects.CorrectedEvent.ann, mem_sdiff, mem_ball, mem_closedBall,
      mem_ofPred_eq, not_le, and_comm] using hm
  have hsep' : Disconnects (P '' Icc t u) A.innerBoundary A.outerBoundary := by
    change LQGMetric.Disconnects (P '' Icc t u) (sphere w a) (sphere w b) at hsep
    exact (disconnects_iff_lqgMetric_disconnects hcurve.isClosed_image).mpr hsep
  exact iInf_le_of_le P (iInf_le_of_le t (iInf_le_of_le u
    (iInf_le_of_le hcurve (iInf_le_of_le htrace'
      (iInf_le_of_le hsep' le_rfl)))))

theorem measurable_around (w : ℂ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    Measurable (fun D : LSCMetric => Objects.CorrectedEvent.around D w a b) := by
  have h := Toolkit.CountableBase.aroundBoundedAnnulus_borel
    (⟨(w, a, b), ha, hab⟩ : EuclideanAnnulus)
  have heq : (fun D : LSCMetric => Objects.CorrectedEvent.around D w a b) =
      (fun D : LSCMetric =>
        aroundDist D (⟨(w, a, b), ha, hab⟩ : EuclideanAnnulus)) := by
    funext D
    exact around_eq_aroundDist D w a b ha hab
  rw [heq]
  exact h

theorem measurableSet_regGood (C : Objects.CorrectedEvent.Constants)
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    (s : ℝ) (hs : 0 < s) (w : ℂ) :
    MeasurableSet {g | Objects.CorrectedEvent.regGood C (D g) s w} := by
  let A : LQGMetric.DistC → ℝ≥0∞ :=
    fun g => Objects.CorrectedEvent.around (D g) w s (2 * s)
  let B : LQGMetric.DistC → ℝ≥0∞ :=
    fun g => Objects.CorrectedEvent.acr (D g) w s (2 * s)
  have hs2 : s < 2 * s := by linarith
  have hA : Measurable A := (measurable_around w s (2 * s) hs hs2).comp hD
  have hB : Measurable B := (measurable_acr w s (2 * s)).comp hD
  change MeasurableSet
    {g | 0 < A g ∧ A g < ⊤ ∧ 0 < B g ∧ B g < ⊤ ∧
      A g ≤ ENNReal.ofReal C.c_reg⁻¹ * B g}
  exact (measurableSet_lt measurable_const hA).inter
    ((measurableSet_lt hA measurable_const).inter
      ((measurableSet_lt measurable_const hB).inter
        ((measurableSet_lt hB measurable_const).inter
          (measurableSet_le hA (measurable_const.mul hB)))))


end SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability
