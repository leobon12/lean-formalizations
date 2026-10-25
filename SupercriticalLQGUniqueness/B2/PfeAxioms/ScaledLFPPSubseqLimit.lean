import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledFiniteMetric
import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledRatioLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteLimit

 




set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric LQGMetric.DFGPS
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_scaled_lfpp_subseq_limit_of_ratio
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (r c : Ioi (0 : ℝ))
    (hc : Tendsto (fun n => (r : ℝ) *
      (m ⟨(ε n : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
      (m (ε n) : ℝ)) atTop (𝓝 (c : ℝ))) :
    let g : Ω → DistC := fun ω => fieldScale r (h ω)
    ∃ Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ δ, IsHeatSmoothing P g δ (Y δ)) ∧
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
            (m ⟨(ε n : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩)
            (Y ⟨(ε n : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ ω)) atTop
          (𝓝 (B2.LscTop.smulMetric
            ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
              Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
            (B2.LscTop.dilate r (D (h ω))))) := by
  dsimp
  obtain ⟨Y, hY, hYeq⟩ :=
    exists_scaled_finite_metric_family P h hh X hX (ξ : ℝ) m r r.property
  refine ⟨Y, hY, ?_⟩
  have hConv := ae_normalizedLFPPMetric_tendsto ξ m ε D hD P h hh X hX
  have hEq : ∀ᵐ ω ∂P, ∀ n,
      PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
        (m ⟨(ε n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩)
        (Y ⟨(ε n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ ω) =
      B2.LscTop.smulMetric
        ⟨((m (ε n) : ℝ) /
          ((r : ℝ) * (m ⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ))) *
          Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
          Set.mem_Ioi.mpr (mul_pos
            (div_pos (m (ε n)).property
              (mul_pos r.property (m ⟨(ε n : ℝ) / (r : ℝ),
                Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩).property))
            (Real.exp_pos _))⟩
        (B2.LscTop.dilate r
          (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))) := by
    exact ae_all_iff.mpr fun n => hYeq (ε n)
  filter_upwards [hConv, hEq] with ω hC hE
  exact tendsto_scaled_metric_of_normalizer_ratio
    (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
    (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
      (m ⟨(ε n : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩)
      (Y ⟨(ε n : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ ω))
    (D (h ω))
    (fun n => (m (ε n) : ℝ))
    (fun n => (m ⟨(ε n : ℝ) / (r : ℝ),
      Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ))
    r c (-(ξ : ℝ) * circleAvg (h ω) r 0)
    (fun n => (m (ε n)).property)
    (fun n => (m ⟨(ε n : ℝ) / (r : ℝ),
      Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩).property)
    r.property c.property hc hC hE

end SupercriticalLQGUniqueness.B2.PfeAxioms
