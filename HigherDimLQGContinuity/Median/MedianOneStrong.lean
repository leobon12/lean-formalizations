import HigherDimLQGContinuity.Frozen.IsMedianOne
import HigherDimLQGMetric.Frozen.Theorem12
import HigherDimLQGMetric.Main.Cor104

/-!
# Median-one strong assignments exist (packet PAR, target B)

Blueprint `a:median-exists` (Part A §1; [C] (1.2), l. 32–36, l. 1297–1309). For `d ≥ 3` and every
subcritical `ξ > 0`, the strong assignment `D⁽¹²⁾` of `HigherDimLQGMetric.theorem12` already has median one:
its normalized convolution LFPP converges to it in probability, locally uniformly, along `ε ↓ 0`, hence
along `εₙ = 1/(n + 2)`, and `HigherDimLQGMetric.l10a_subseq_limit_median_one` identifies the median of
`D⁽¹²⁾_h(0, e₁)` under `normLGFLaw d` as `1`. No rescaling is needed.

Main statement: `medianOneStrong_holds` (the frozen statement of `medianOneStrong_exists`, verbatim).
Helper: `isMedianOne_iff_isMedian` (the set form `IsMedianOne` is the median of the push-forward law, for a
measurable assignment).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- For a measurable assignment `E`, the set form `IsMedianOne d E` is the statement that `1` is a median
of the law of `E_g(0, e₁)` under `normLGFLaw d`. -/
theorem isMedianOne_iff_isMedian {d : ℕ} {E : DistRd d → ContMetric d} (hE : Measurable E) :
    IsMedianOne d E ↔
      LQGMetric.IsMedian ((normLGFLaw d).map fun g => (E g).1 (0, e₁ d)) 1 := by
  have hX : Measurable fun g => (E g).1 (0, e₁ d) :=
    (ContinuousMap.measurable_eval (0, e₁ d)).comp (measurable_subtype_coe.comp hE)
  rw [LQGMetric.isMedian_iff, Measure.map_apply hX measurableSet_Iic,
    Measure.map_apply hX measurableSet_Ici]
  rfl

/-- `εₙ = 1/(n + 2)` tends to `0` from the right. -/
theorem par_tendsto_inv_nat_add_two :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  · exact (one_div_pos.2 (by positivity) : (0 : ℝ) < 1 / ((n : ℝ) + 2))

/-- **Target B** (the frozen statement of `medianOneStrong_exists`, verbatim): for `d ≥ 3` and every
subcritical `ξ > 0` there is a strong assignment at `(ξ, Q(ξ))` with median one. -/
theorem medianOneStrong_holds :
    ∀ d : ℕ, 3 ≤ d → ∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E ∧ IsMedianOne d E := by
  intro d hd ξ hξ hsub
  obtain ⟨⟨D, hD, hconv⟩, -⟩ := theorem12 d ξ hd hξ hsub
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  refine ⟨D, hD, (isMedianOne_iff_isMedian hD.measurable).2 ?_⟩
  exact l10a_subseq_limit_median_one (by omega) hκ ξ (fun n : ℕ => 1 / ((n : ℝ) + 2))
    (fun n => (one_div_pos.2 (by positivity) : (0 : ℝ) < 1 / ((n : ℝ) + 2)))
    (fun P _ h hh R hR δ hδ => (hconv κ hκ P h hh R hR δ hδ).comp par_tendsto_inv_nat_add_two)

end HigherDimLQGContinuity
