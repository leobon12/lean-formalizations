import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath.DeterministicGap
import LQGMetric.Field.MeasurableAvg




 
set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath

 

theorem measurable_setDist_closedBalls (z w : ℂ) (s : ℝ) :
    Measurable fun d : LSCMetric =>
      OptimalConstants.Ratios.setDist d (Metric.closedBall z s) (Metric.closedBall w s) := by
  have hK : IsCompact
      (Metric.closedBall z s ×ˢ Metric.closedBall w s) :=
    (isCompact_closedBall z s).prod (isCompact_closedBall w s)
  simpa only [OptimalConstants.Ratios.setDist_eq_iInf_prod] using
    LSCMetric.measurable_iInf_of_isCompact hK

 



def closedSavingVersion {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cPlus : ℝ≥0∞) (b ν δ κ : Set.Ioi (0 : ℝ)) : Set Ω :=
  {ω | ∀ i j : ℤ × ℤ,
    let s := (δ : ℝ) ^ (ν : ℝ) * (b : ℝ)
    let z := LQGMetric.GM.gridPt (s / 100) i
    let w := LQGMetric.GM.gridPt (s / 100) j
    z ∈ Metric.ball (0 : ℂ) b → w ∈ Metric.ball (0 : ℂ) b →
    κ * (b : ℝ) ≤ dist z w →
    κ * (b : ℝ) ≤ Metric.infDist z (Metric.sphere (0 : ℂ) b) →
    OptimalConstants.Ratios.setDist (D' (h ω)) (Metric.closedBall z s) (Metric.closedBall w s) +
      ENNReal.ofReal (δ * (b : ℝ) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * LQGMetric.circleAvg (h ω) b 0)) <
      cPlus * OptimalConstants.Ratios.setDist (D (h ω))
        (Metric.closedBall z s) (Metric.closedBall w s)}

theorem measurable_closedSavingVersion {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → DistC) (hh : Measurable h)
    (D D' : DistC → LSCMetric) (hD : Measurable D) (hD' : Measurable D')
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cPlus : ℝ≥0∞)
    (b ν δ κ : Set.Ioi (0 : ℝ)) :
    MeasurableSet (closedSavingVersion h D D' ξ Q cPlus b ν δ κ) := by
  simp only [closedSavingVersion, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  refine MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
  apply measurableSet_lt
  · apply Measurable.add
    · exact (measurable_setDist_closedBalls _ _ _).comp (hD'.comp hh)
    · apply Measurable.ennreal_ofReal
      exact measurable_const.mul ((measurable_const.mul
        ((LQGMetric.measurable_circleAvg_left (b : ℝ) 0).comp hh)).exp)
  · exact measurable_const.mul
      ((measurable_setDist_closedBalls _ _ _).comp (hD.comp hh))

 

theorem closedSaving_ae_eq {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cPlus : ℝ≥0∞)
    (b ν δ κ : Set.Ioi (0 : ℝ))
    (hCircle : ∀ᵐ ω ∂P,
      IsCircleAverage (h ω) b 0 (LQGMetric.circleAvg (h ω) b 0)) :
    P (EndSaving.Interfaces.ClosedEndSaving h D D' ξ Q cPlus b ν δ κ) =
      P (closedSavingVersion h D D' ξ Q cPlus b ν δ κ) := by
  have heq : ∀ᵐ ω ∂P,
      (ω ∈ EndSaving.Interfaces.ClosedEndSaving h D D' ξ Q cPlus b ν δ κ ↔
        ω ∈ closedSavingVersion h D D' ξ Q cPlus b ν δ κ) := by
    filter_upwards [hCircle] with ω hω
    constructor
    · rintro ⟨hbr, hbrCircle, hSave⟩
      have hbrEq : hbr = LQGMetric.circleAvg (h ω) b 0 :=
        tendsto_nhds_unique hbrCircle hω
      simpa only [closedSavingVersion, Set.mem_ofPred_eq, hbrEq] using hSave
    · intro hSave
      exact ⟨LQGMetric.circleAvg (h ω) b 0, hω,
        by simpa only [closedSavingVersion, Set.mem_ofPred_eq] using hSave⟩
  exact (measure_mono_ae (heq.mono fun _ h => h.mp)).antisymm
    (measure_mono_ae (heq.mono fun _ h => h.mpr))



end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath
