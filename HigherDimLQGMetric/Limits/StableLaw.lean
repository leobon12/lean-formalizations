import HigherDimLQGMetric.B3.Interfaces
import LQGMetric.Prob.PolishContinuousMap
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Marginal consequences of stable LFPP convergence

The interface's `StablyTendstoLU` implies convergence of the metric laws.  The
fixed field marginal will later permit adjoining its measurable observables.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Stable convergence gives weak convergence of the metric marginals. -/
theorem l6c_stable_metric_law {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ)) (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hstable : StablyTendstoLU P h X Y)
    (ν : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (μ : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (hν : ∀ n, (ν n : Measure C(Rd d × Rd d, ℝ)) = P.map (X n))
    (hμ : (μ : Measure C(Rd d × Rd d, ℝ)) = P.map Y) :
    Tendsto ν atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  have ht := hstable (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
    φ φ.continuous ⟨‖φ‖, fun D => by
      simpa only [Real.norm_eq_abs] using φ.norm_coe_le_norm D⟩
  simp_rw [hν, hμ, integral_map (hX _) φ.continuous.measurable.aestronglyMeasurable]
  rw [integral_map hY φ.continuous.measurable.aestronglyMeasurable]
  simpa only [one_mul] using ht

/-- Stable convergence persists along every strictly increasing subsequence. -/
theorem l6c_stable_subseq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ)) (Y : Ω → C(Rd d × Rd d, ℝ))
    (hstable : StablyTendstoLU P h X Y)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    StablyTendstoLU P h (fun n => X (φ n)) Y := by
  intro g hg hgb ψ hψ hψb
  exact (hstable g hg hgb ψ hψ hψb).comp hφ.tendsto_atTop

end HigherDimLQGMetric
