import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.FiniteStableMeas
import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.CompactSetDist




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
open LQGMetric (DistC)

def FbarStaticV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) : Prop :=
  Z.Nonempty ∧ EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧
  IsCircleAverage g b 0 (Measurability.ClauseEvents.circleValue b 0 g) ∧
  OptimalConstants.Ratios.setDist (D' g) K₁ K₂ ≥
    cPlus * OptimalConstants.Ratios.setDist (D g) K₁ K₂ -
      ENNReal.ofReal ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * Measurability.ClauseEvents.circleValue b 0 g)) ∧
  ∀ i ∈ Z, g ∈ (obj i).E ∧
    IsCircleAverage g r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
      (Measurability.ClauseEvents.circleValue r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) g) ∧
    EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q
      (Measurability.ClauseEvents.circleValue r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) g)
      (Measurability.ClauseEvents.circleValue b 0 g)

theorem fbarStaticV2_measurable {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D')
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) :
    MeasurableSet {g : DistC |
      FbarStaticV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g} := by
  let B : DistC → ℝ := fun g =>
    (q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * Measurability.ClauseEvents.circleValue b 0 g)
  have hB : Measurable B := by
    exact measurable_const.mul
      (Real.measurable_exp.comp
        (measurable_const.mul (Measurability.ClauseEvents.circleValue_measurable b 0)))
  let B2 : DistC → ℝ := fun g =>
    2 * (q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * Measurability.ClauseEvents.circleValue b 0 g)
  have hB2 : Measurable B2 := by
    exact measurable_const.mul
      (Real.measurable_exp.comp
        (measurable_const.mul (Measurability.ClauseEvents.circleValue_measurable b 0)))
  have hdist : Measurable (fun g : DistC => OptimalConstants.Ratios.setDist (D g) K₁ K₂) :=
    (Measurability.ClauseEvents.measurable_setDist_compact K₁ K₂ hK₁ hK₂).comp hD
  have hdist' : Measurable (fun g : DistC => OptimalConstants.Ratios.setDist (D' g) K₁ K₂) :=
    (Measurability.ClauseEvents.measurable_setDist_compact K₁ K₂ hK₁ hK₂).comp hD'
  have hbad : MeasurableSet {g : DistC |
      cPlus * OptimalConstants.Ratios.setDist (D g) K₁ K₂ - ENNReal.ofReal (B g) ≤
        OptimalConstants.Ratios.setDist (D' g) K₁ K₂} :=
    measurableSet_le ((measurable_const.mul hdist).sub
      (ENNReal.measurable_ofReal.comp hB)) hdist'
  have hlocal (i : ℤ × ℤ) : MeasurableSet {g : DistC |
      g ∈ (obj i).E ∧
      IsCircleAverage g r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
        (Measurability.ClauseEvents.circleValue r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) g) ∧
      EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q
        (Measurability.ClauseEvents.circleValue r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) g)
        (Measurability.ClauseEvents.circleValue b 0 g)} := by
    let z := LQGMetric.GM.gridPt ((r : ℝ) / 100) i
    have hN : Measurable (fun g : DistC =>
        (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * Measurability.ClauseEvents.circleValue r z g)) :=
      measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul (Measurability.ClauseEvents.circleValue_measurable r z)))
    have hsize : MeasurableSet {g : DistC |
        EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q
          (Measurability.ClauseEvents.circleValue r z g) (Measurability.ClauseEvents.circleValue b 0 g)} := by
      change MeasurableSet {g : DistC |
        B g ≤ (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * Measurability.ClauseEvents.circleValue r z g) ∧
        (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * Measurability.ClauseEvents.circleValue r z g) ≤ B2 g}
      exact (measurableSet_le hB hN).inter
        (measurableSet_le hN hB2)
    exact (obj i).E_measurable.inter
      ((Measurability.ClauseEvents.circleValue_graph_measurable r z).inter hsize)
  have hall : MeasurableSet {g : DistC | ∀ i ∈ Z,
      g ∈ (obj i).E ∧
      IsCircleAverage g r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
        (Measurability.ClauseEvents.circleValue r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) g) ∧
      EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q
        (Measurability.ClauseEvents.circleValue r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) g)
        (Measurability.ClauseEvents.circleValue b 0 g)} := by
    convert Z.measurableSet_biInter (fun i _ => hlocal i) using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  by_cases hfixed : Z.Nonempty ∧ EndSaving.Interfaces.Configuration r b K₁ K₂ Z
  · have hcore := (Measurability.ClauseEvents.circleValue_graph_measurable b 0).inter
        (hbad.inter hall)
    convert hcore using 1
    ext g
    simp only [FbarStaticV2, hfixed, true_and, Set.mem_inter_iff,
      Set.mem_ofPred_eq, B, ge_iff_le]
  · have hempty : {g : DistC |
        FbarStaticV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g} = ∅ := by
      ext g
      simp only [FbarStaticV2, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]
      intro hbad'
      exact hfixed ⟨hbad'.1, hbad'.2.1⟩
    rw [hempty]
    exact MeasurableSet.empty

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
