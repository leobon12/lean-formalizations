import SupercriticalLQGUniqueness.B2.DG20Lim.OpenEventLimitProbability

 

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem isOpen_finite_bad_ratio
    (A : ℕ → RatAnnulus) (S : Finset ℕ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) :
    IsOpen {v : (CoordJ → ℝ) × RatCoords | ∀ i ∈ S,
      C * v.2.1 ((A i).inner, (A i).outer) < v.2.2 (A i)} := by
  classical
  have heq : {v : (CoordJ → ℝ) × RatCoords | ∀ i ∈ S,
      C * v.2.1 ((A i).inner, (A i).outer) < v.2.2 (A i)} =
      ⋂ i ∈ S, {v : (CoordJ → ℝ) × RatCoords |
        C * v.2.1 ((A i).inner, (A i).outer) < v.2.2 (A i)} := by
    ext v
    simp only [mem_setOf_eq, mem_iInter]
  rw [heq]
  apply isOpen_biInter_finset
  intro i hi
  have hAcross : Continuous fun v : (CoordJ → ℝ) × RatCoords =>
      v.2.1 ((A i).inner, (A i).outer) :=
    (continuous_apply ((A i).inner, (A i).outer)).comp
      (continuous_fst.comp continuous_snd)
  have hAround : Continuous fun v : (CoordJ → ℝ) × RatCoords =>
      v.2.2 (A i) :=
    (continuous_apply (A i)).comp (continuous_snd.comp continuous_snd)
  exact isOpen_lt ((ENNReal.continuous_const_mul hC).comp hAcross) hAround

end SupercriticalLQGUniqueness.B2.DG20Lim
