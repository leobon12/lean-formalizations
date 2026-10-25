import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Cor




 





set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace Uniqueness.BiLipschitz.Barrier

open LQGMetric (DistC)

 

theorem measurableSet_barrier {D : DistC → LSCMetric} (hD : Measurable D) :
    MeasurableSet {g : DistC | Barrier (D g)} := by
  have hm : ∀ n, Measurable fun g => acrossDist (D g) (dyadicAnnulus n) := fun n =>
    (measurable_acrossDist (dyadicAnnulus n)).comp hD
  have heq : {g : DistC | Barrier (D g)} = ⋂ n₀ : ℕ, ⋂ M : ℕ, ⋃ n : ℕ,
      ({_g : DistC | n₀ ≤ n} ∩ {g | (M : ℝ≥0∞) < acrossDist (D g) (dyadicAnnulus n)}) := by
    ext g
    simp only [Barrier, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
  rw [heq]
  refine MeasurableSet.iInter fun n₀ => MeasurableSet.iInter fun M =>
    MeasurableSet.iUnion fun n => ?_
  exact (MeasurableSet.const _).inter (measurableSet_lt measurable_const (hm n))

end Uniqueness.BiLipschitz.Barrier
end SupercriticalLQGUniqueness
