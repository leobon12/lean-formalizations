import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Block
import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.CostMeas




 






set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality

open LQGMetric (DistC)

 
theorem measurableSet_shieldAt (C : Objects.CorrectedEvent.Constants)
    (D : DistC → LSCMetric) (hD : Measurable D) (t : ℝ) (ht : 0 < t) :
    MeasurableSet {g | Objects.Excursions.shieldAt C (D g) t} := by
  let A : DistC → ℝ≥0∞ := fun g => Objects.CorrectedEvent.around (D g) 0 t (2 * t)
  let B : DistC → ℝ≥0∞ := fun g => Objects.CorrectedEvent.acr (D g) 0 (2 * t) (3 * t)
  have htt : t < 2 * t := by linarith
  have hA : Measurable A := (Objects.ClauseMeasurability.measurable_around 0 t (2 * t) ht htt).comp hD
  have hB : Measurable B := (Objects.ClauseMeasurability.measurable_acr 0 (2 * t) (3 * t)).comp hD
  change MeasurableSet {g | A g < ⊤ ∧ A g ≤ ENNReal.ofReal C.lamConst * B g}
  exact (measurableSet_lt hA measurable_const).inter
    (measurableSet_le hA (measurable_const.mul hB))

 
theorem measurableSet_shield (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (Ksh : ℕ) (D : DistC → LSCMetric) (hD : Measurable D)
    (hρr : 0 < T.rho * T.r) :
    MeasurableSet {g | Objects.Excursions.shield C T Ksh (D g)} := by
  classical
  have heq : {g | Objects.Excursions.shield C T Ksh (D g)} =
      ⋃ k ∈ Finset.Icc 1 Ksh,
        {g | Objects.Excursions.shieldAt C (D g) (3 * 8 ^ (Ksh - k) * (T.rho * T.r))} := by
    ext g
    simp only [Objects.Excursions.shield, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [heq]
  refine Finset.measurableSet_biUnion _ (fun k _ => ?_)
  have ht : 0 < 3 * 8 ^ (Ksh - k) * (T.rho * T.r) := by
    exact mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _)) hρr
  exact measurableSet_shieldAt C D hD _ ht

end SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality
