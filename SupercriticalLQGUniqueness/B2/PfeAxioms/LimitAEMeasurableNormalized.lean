import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteLimit
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem aemeasurable_limit_metric_normalized
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    AEMeasurable (fun ω => D (h ω)) P := by
  have hG : ∀ n, AEMeasurable
      (fun ω => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
        (m (ε n)) (X (ε n) ω)) P := by
    intro n
    have hmG : Measurable (fun φ : C(ℂ, ℝ) =>
        PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) φ) :=
      measurable_normalizedLFPPMetric_comp (ξ : ℝ) (m (ε n))
        (fun z => (continuous_eval_const z).measurable)
    exact hmG.comp_aemeasurable
      (aemeasurable_heat_smoothing_version P h hh (ε n) (X (ε n)) (hX (ε n)))
  exact B2.LscTop.aemeasurable_of_tendsto_lscMetric_ae hG
    (ae_normalizedLFPPMetric_tendsto ξ m ε D hD P h hh X hX)

end SupercriticalLQGUniqueness.B2.PfeAxioms
