import HigherDimLQGMetric.Limits.Median
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Uniform positivity of lower medians on compact sets of laws

This is the compactness step needed in the corrected scaling argument.  A
positive observable has a positive lower median under each law, and
portmanteau prevents these medians from approaching zero within a compact
family of laws.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

/-- Positive lower medians are bounded uniformly away from zero on a compact
family of probability laws. -/
theorem l6c_uniform_lowerMedian_pos {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
    (K : Set (ProbabilityMeasure E)) (hK : IsCompact K)
    (e : E → ℝ) (he : Continuous e)
    (hpos : ∀ μ ∈ K, ∀ᵐ x ∂(μ : Measure E), 0 < e x) :
    ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ K, c ≤ lowerMedian (μ : Measure E) e := by
  classical
  by_contra hbad
  have hchoose (c : ℝ) (hc : 0 < c) :
      ∃ μ ∈ K, lowerMedian (μ : Measure E) e < c := by
    by_contra hn
    apply hbad
    refine ⟨c, hc, fun μ hμ => ?_⟩
    exact le_of_not_gt (fun hh => hn ⟨μ, hμ, hh⟩)
  let μs : ℕ → ProbabilityMeasure E := fun n =>
    Classical.choose (hchoose (1 / (n + 1 : ℝ)) (by positivity))
  have hμs (n : ℕ) : μs n ∈ K :=
    (Classical.choose_spec (hchoose (1 / (n + 1 : ℝ)) (by positivity))).1
  have hmeds (n : ℕ) : lowerMedian (μs n : Measure E) e < 1 / (n + 1 : ℝ) :=
    (Classical.choose_spec (hchoose (1 / (n + 1 : ℝ)) (by positivity))).2
  obtain ⟨μ, hμ, φ, hφ, hlim⟩ := hK.tendsto_subseq hμs
  have hmed : 0 < lowerMedian (μ : Measure E) e :=
    l6c_lowerMedian_pos he.measurable.aemeasurable (hpos μ hμ)
  let δ : ℝ := lowerMedian (μ : Measure E) e / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let F : Set E := {x | e x ≤ δ}
  have hF : IsClosed F := isClosed_Iic.preimage he
  have hFlt : (μ : Measure E) F < (2 : ℝ≥0∞)⁻¹ := by
    have hn : ¬ (2 : ℝ≥0∞)⁻¹ ≤ (μ : Measure E) F := by
      intro hh
      have hq := (l6c_half_le_measure_iff_lowerMedian_le
        (P := (μ : Measure E)) he.measurable.aemeasurable).mp hh
      dsimp [F, δ] at hq
      linarith
    exact lt_of_not_ge hn
  have hsmall : Tendsto (fun n : ℕ => (1 : ℝ) / (φ n + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  have hev : ∀ᶠ n in atTop,
      (2 : ℝ≥0∞)⁻¹ ≤ (μs (φ n) : Measure E) F := by
    filter_upwards [hsmall.eventually (gt_mem_nhds hδ)] with n hn
    apply (l6c_half_le_measure_iff_lowerMedian_le
      (P := (μs (φ n) : Measure E)) he.measurable.aemeasurable).mpr
    exact (hmeds (φ n)).le.trans hn.le
  have hlimF := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤
      limsup (fun n => (μs (φ n) : Measure E) F) atTop := by
    simpa only [limsup_const] using
      (limsup_le_limsup hev (u := fun _ : ℕ => (2 : ℝ≥0∞)⁻¹))
  exact (not_le_of_gt hFlt) (hhalf.trans hlimF)

/-- An upper bound for a lower median passes to the weak closure of laws when
the underlying observable is continuous. -/
theorem l6c_lowerMedian_le_of_closure {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
    (S : Set (ProbabilityMeasure E)) (e : E → ℝ) (he : Continuous e)
    (b : ℝ) (hb : ∀ ν ∈ S, lowerMedian (ν : Measure E) e ≤ b)
    (μ : ProbabilityMeasure E) (hμ : μ ∈ closure S) :
    lowerMedian (μ : Measure E) e ≤ b := by
  let F : Set E := {x | e x ≤ b}
  have hF : IsClosed F := isClosed_Iic.preimage he
  obtain ⟨νs, hνs, hlim⟩ := mem_closure_iff_seq_limit.mp hμ
  have hmass (n : ℕ) : (2 : ℝ≥0∞)⁻¹ ≤ (νs n : Measure E) F :=
    (l6c_half_le_measure_iff_lowerMedian_le
      (P := (νs n : Measure E)) he.measurable.aemeasurable).mpr
      (hb (νs n) (hνs n))
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤
      limsup (fun n => (νs n : Measure E) F) atTop := by
    simpa only [limsup_const] using
      (limsup_le_limsup (f := atTop) (Filter.Eventually.of_forall hmass)
        (u := fun _ : ℕ => (2 : ℝ≥0∞)⁻¹))
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  exact (l6c_half_le_measure_iff_lowerMedian_le
    (P := (μ : Measure E)) he.measurable.aemeasurable).mp (hhalf.trans hle)

end HigherDimLQGMetric
