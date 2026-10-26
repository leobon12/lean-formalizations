import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# A sequence criterion at a positive cutoff

This is the scalar specialization of the filter argument used by
`SupercriticalLQGUniqueness.B2.LscTop.lscTendstoInProbability_iff_tendstoInMeasure`.
It turns convergence in measure along every positive sequence tending to zero
into convergence in measure along the positive cutoff filter.
-/

set_option autoImplicit false

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace SupercriticalLFPPAS

/-- Convergence in measure along every positive sequence tending to zero implies
convergence in measure as the positive cutoff tends to zero. -/
theorem tendstoInMeasure_positiveCutoff_of_seq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {f : Set.Ioi (0 : ℝ) → Ω → ℝ≥0} {g : Ω → ℝ≥0}
    (h : ∀ e : ℕ → Set.Ioi (0 : ℝ),
      Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0) →
        TendstoInMeasure P (fun n => f (e n)) atTop g) :
    TendstoInMeasure P f (comap Subtype.val (𝓝 (0 : ℝ))) g := by
  intro δ hδ
  refine tendsto_iff_seq_tendsto.2 fun e he => ?_
  exact h e (tendsto_comap_iff.1 he) δ hδ

end SupercriticalLFPPAS
