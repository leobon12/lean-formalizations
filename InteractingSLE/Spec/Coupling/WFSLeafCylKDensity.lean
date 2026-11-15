/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafCylKWindow
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Metrizable.Real

/-!
# L¹ density of bounded continuous finite history cylinders

Mathlib supplies bounded continuous approximation on the full history space.
Continuous finite-window filling and dominated convergence reduce each such
approximant to a bounded continuous observable of finitely many coordinates.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace InteractingSLE.WFS

open LawUnique

/-- Bounded continuous window observables of a measurable history are integrable. -/
theorem integrable_historyWindow_comp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {nL nR n : ℕ} {Y : Ω → HistorySpace nL nR} (hY : Measurable Y)
    (g : HistoryWindow nL nR n →ᵇ ℝ) :
    Integrable (fun ω => g (historyWindow n (Y ω))) P :=
  Integrable.of_bound (g.continuous.measurable.comp
    ((measurable_historyWindow n).comp hY)).aestronglyMeasurable ‖g‖
    (ae_of_all _ fun _ => g.norm_coe_le_norm _)

/-- The L¹ error of filling a bounded continuous full-history observable
from longer finite windows tends to zero. -/
theorem tendsto_integral_historyFill_window
    {nL nR : ℕ} {μ : Measure (HistorySpace nL nR)} [IsFiniteMeasure μ]
    (f : HistorySpace nL nR →ᵇ ℝ) :
    Tendsto (fun n => ∫ γ, ‖f γ - f (historyFill (historyWindow n γ))‖ ∂μ)
      atTop (𝓝 0) := by
  have he (n : ℕ) : Continuous (fun γ : HistorySpace nL nR =>
      ‖f γ - f (historyFill (historyWindow n γ))‖) :=
    (f.continuous.sub (f.continuous.comp
      (continuous_historyFill.comp (continuous_historyWindow n)))).norm
  have hl (γ : HistorySpace nL nR) :
      Tendsto (fun n => ‖f γ - f (historyFill (historyWindow n γ))‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, Function.comp_def] using
      ((tendsto_const_nhds (x := f γ)).sub ((f.continuous.tendsto γ).comp
        (tendsto_historyFill_window γ))).norm
  have hb (n : ℕ) (γ : HistorySpace nL nR) :
      ‖‖f γ - f (historyFill (historyWindow n γ))‖‖ ≤ 2 * ‖f‖ := by
    rw [norm_norm]
    exact (norm_sub_le _ _).trans
      ((add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)).trans_eq (two_mul ‖f‖).symm)
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun _ => 2 * ‖f‖)
      (fun n => (he n).measurable.aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ (hb n)) (ae_of_all _ hl)

/-- Every integrable full-history observable has arbitrarily accurate L¹
approximations by bounded continuous finite-window observables. -/
theorem exists_historyWindow_L1_approx
    {nL nR : ℕ} {μ : Measure (HistorySpace nL nR)} [IsFiniteMeasure μ]
    {F : HistorySpace nL nR → ℝ} (hF : Integrable F μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ g : HistoryWindow nL nR n →ᵇ ℝ,
      (∫ γ, ‖F γ - g (historyWindow n γ)‖ ∂μ) < ε := by
  let : μ.WeaklyRegular :=
    Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure μ
  obtain ⟨f, hfe, hfi⟩ := hF.exists_boundedContinuous_integral_sub_le
    (ε := ε / 3) (by positivity)
  obtain ⟨n, hn⟩ := ((tendsto_integral_historyFill_window (μ := μ) f).eventually
    (Iio_mem_nhds (show 0 < ε / 3 by positivity))).exists
  let g : HistoryWindow nL nR n →ᵇ ℝ :=
    f.compContinuous ⟨historyFill, continuous_historyFill⟩
  have hgi : Integrable (fun γ => g (historyWindow n γ)) μ :=
    integrable_historyWindow_comp measurable_id g
  refine ⟨n, g, ?_⟩
  calc
    _ ≤ ∫ γ, ‖F γ - f γ‖ + ‖f γ - g (historyWindow n γ)‖ ∂μ := by
      apply integral_mono (hF.sub hgi).norm ((hF.sub hfi).norm.add (hfi.sub hgi).norm)
      intro γ
      dsimp only [Pi.sub_apply, Pi.add_apply]
      simpa only [dist_eq_norm] using dist_triangle (F γ) (f γ) (g (historyWindow n γ))
    _ = (∫ γ, ‖F γ - f γ‖ ∂μ) + ∫ γ, ‖f γ - g (historyWindow n γ)‖ ∂μ :=
      integral_add (hF.sub hfi).norm (hfi.sub hgi).norm
    _ < ε / 3 + ε / 3 := add_lt_add_of_le_of_lt hfe hn
    _ < ε := by linarith only [hε]

end InteractingSLE.WFS
