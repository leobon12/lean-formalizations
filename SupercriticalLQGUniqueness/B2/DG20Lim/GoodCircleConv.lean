import SupercriticalLQGUniqueness.B2.DG20Lim.TriangleLimit
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

 


set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.good_annulus_costs_tendsto_zero (R : RData)
    (A : ℕ → RatAnnulus) (C M : ℝ≥0∞)
    (hC : C ≠ ∞) (hM : M ≠ ∞)
    (hGood : ∀ n,
      R.around (A n) ≤ C * R.across (A n).inner (A n).outer)
    (hSum : ∀ N,
      (∑ n ∈ Finset.range N,
        R.across (A n).inner (A n).outer) ≤ M) :
    Tendsto (fun n => R.across (A n).inner (A n).outer)
      atTop (𝓝 0) ∧
    Tendsto (fun n => R.around (A n)) atTop (𝓝 0) := by
  have htsum : (∑' n, R.across (A n).inner (A n).outer) ≠ ∞ :=
    ne_of_lt ((ENNReal.tsum_le_of_sum_range_le hSum).trans_lt
      (lt_top_iff_ne_top.mpr hM))
  have hCross := ENNReal.tendsto_atTop_zero_of_tsum_ne_top htsum
  refine ⟨hCross, ?_⟩
  have hUpper : Tendsto
      (fun n => C * R.across (A n).inner (A n).outer)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hCross (Or.inr hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hUpper (fun _ => zero_le) hGood

end SupercriticalLQGUniqueness.B2.DG20Lim
