import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.EMetricSpace.Weak

/-!
# Convergence in measure for extended nonnegative reals

The usual extended distance on `ℝ≥0∞` is only a weak extended metric.  This
file transports convergence in measure from `ℝ≥0` when all approximating
values are finite and the limit is almost surely finite.
-/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace SupercriticalLFPPAS

/-- Convergence in measure of finite `ℝ≥0∞`-valued maps, for Mathlib's
standard weak extended distance, follows from convergence in measure after
`ENNReal.toNNReal`. -/
theorem tendstoInMeasure_ennreal_of_toNNReal
    {Ω ι : Type} [MeasurableSpace Ω] {P : Measure Ω} {l : Filter ι}
    (f : ι → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞)
    (hf : ∀ i ω, f i ω ≠ ∞) (hg : ∀ᵐ ω ∂P, g ω ≠ ∞)
    (h : TendstoInMeasure P (fun i ω => (f i ω).toNNReal) l
      (fun ω => (g ω).toNNReal)) :
    TendstoInMeasure P f l g := by
  intro ε hε
  by_cases hεtop : ε = ∞
  · have hz : ∀ i, P {ω | ε ≤ edist (f i ω) (g ω)} = 0 := by
      intro i
      have hzero : {ω | ε ≤ edist (f i ω) (g ω)} =ᵐ[P] ∅ := by
        filter_upwards [hg] with ω hω
        simp [hεtop, ENNReal.edist_eq_top_iff, hf i ω, hω]
      simpa using measure_congr hzero
    have heq : (fun i => P {ω | ε ≤ edist (f i ω) (g ω)}) =
        fun _ : ι => (0 : ℝ≥0∞) := funext hz
    rw [heq]
    exact tendsto_const_nhds
  · let δ : ℝ≥0 := ε.toNNReal
    have hδ : 0 < δ := ENNReal.toNNReal_pos (ne_of_gt hε) hεtop
    have hconv := h (δ : ℝ≥0∞) (ENNReal.coe_pos.2 hδ)
    have hmeas : ∀ i, P {ω | ε ≤ edist (f i ω) (g ω)} =
        P {ω | δ ≤ edist (f i ω).toNNReal (g ω).toNNReal} := by
      intro i
      apply measure_congr
      filter_upwards [hg] with ω hω
      rw [← ENNReal.coe_toNNReal (hf i ω), ← ENNReal.coe_toNNReal hω,
        ← ENNReal.coe_toNNReal hεtop]
      rfl
    simpa only [hmeas] using hconv

/-- For finite `ℝ≥0∞`-valued maps, convergence in measure for Mathlib's
standard weak extended distance passes through `ENNReal.toNNReal`. -/
theorem tendstoInMeasure_toNNReal_of_ennreal
    {Ω ι : Type} [MeasurableSpace Ω] {P : Measure Ω} {l : Filter ι}
    (f : ι → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞)
    (hf : ∀ i ω, f i ω ≠ ∞) (hg : ∀ᵐ ω ∂P, g ω ≠ ∞)
    (h : TendstoInMeasure P f l g) :
    TendstoInMeasure P (fun i ω => (f i ω).toNNReal) l
      (fun ω => (g ω).toNNReal) := by
  intro δ hδ
  have hconv := h δ hδ
  have hmeas : ∀ i,
      P {ω | δ ≤ edist (f i ω).toNNReal (g ω).toNNReal} =
        P {ω | δ ≤ edist (f i ω) (g ω)} := by
    intro i
    apply measure_congr
    filter_upwards [hg] with ω hω
    rw [← ENNReal.coe_toNNReal (hf i ω), ← ENNReal.coe_toNNReal hω]
    rfl
  simpa only [hmeas] using hconv

end SupercriticalLFPPAS
