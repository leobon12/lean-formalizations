import BouRabeeGwynne.DiscreteHarmonicMeasure

/-!
# The exit-probability lower bound forced by a spike

This is the finite probability calculation in (5.11)--(5.12). It applies to
the actual exit law once the mean-value and terminal-location facts are supplied.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BouRabeeGwynne

/-- A mean-value identity and a gap on the complement of E force a positive
probability of E. The value `b` is the continuum value at the starting vertex. -/
theorem mesh_only_spike_probability_lower_bound
    {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (μ : Measure V) [IsProbabilityMeasure μ] (E : Set V) (f : V → ℝ)
    {b α H : ℝ} (hα : 0 < α) (hH : 0 ≤ H) (hb : -H ≤ b)
    (hmean : b + α ≤ ∫ w, f w ∂μ)
    (hmax : ∀ w, f w ≤ H)
    (hsmall : ∀ᵐ w ∂μ, w ∉ E → f w ≤ b + 3 * α / 4) :
    (α / 4) / (2 * H + 3 * α / 4) ≤ (μ E).toReal := by
  classical
  let c : ℝ := b + 3 * α / 4
  let K : ℝ := 2 * H + 3 * α / 4
  have hK : 0 < K := by dsimp [K]; positivity
  have hpoint : ∀ᵐ w ∂μ, f w ≤ c + E.indicator (fun _ => K) w := by
    filter_upwards [hsmall] with w hwsmall
    by_cases hw : w ∈ E
    · rw [Set.indicator_of_mem hw]
      have hwH := hmax w
      dsimp [c, K]
      linarith
    · rw [Set.indicator_of_notMem hw, add_zero]
      exact hwsmall hw
  have hint : (∫ w, f w ∂μ) ≤ c + (μ E).toReal * K := by
    calc
      _ ≤ ∫ w, c + E.indicator (fun _ => K) w ∂μ :=
        integral_mono_ae Integrable.of_finite Integrable.of_finite hpoint
      _ = _ := by
        rw [integral_add Integrable.of_finite Integrable.of_finite,
          integral_const, integral_indicator_const K (Set.toFinite E).measurableSet]
        simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  apply (div_le_iff₀ hK).mpr
  dsimp [c] at hint
  linarith

end BouRabeeGwynne
