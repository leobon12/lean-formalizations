import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledHeatVersion
import SupercriticalLQGUniqueness.B2.PfeAxioms.FiniteDilationLFPP

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.DFGPS
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_scaled_finite_metric_family
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ξ : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (r : ℝ) (hr : 0 < r) :
    let g : Ω → DistC := fun ω => fieldScale r (h ω)
    ∃ Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ δ, IsHeatSmoothing P g δ (Y δ)) ∧
      ∀ ε : Ioi (0 : ℝ), ∀ᵐ ω ∂P,
        PfeWeyl.normalizedLFPPMetric ξ
          (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.property hr)⟩)
          (Y ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.property hr)⟩ ω) =
        B2.LscTop.smulMetric
          ⟨((m ε : ℝ) /
              (r * (m ⟨(ε : ℝ) / r,
                Set.mem_Ioi.mpr (div_pos ε.property hr)⟩ : ℝ))) *
              Real.exp (-ξ * circleAvg (h ω) r 0),
            Set.mem_Ioi.mpr (mul_pos
              (div_pos (m ε).property
                (mul_pos hr (m ⟨(ε : ℝ) / r,
                  Set.mem_Ioi.mpr (div_pos ε.property hr)⟩).property))
              (Real.exp_pos _))⟩
          (B2.LscTop.dilate ⟨r, Set.mem_Ioi.mpr hr⟩
            (PfeWeyl.normalizedLFPPMetric ξ (m ε) (X ε ω))) := by
  dsimp
  obtain ⟨Y, hY, hYeq⟩ := exists_scaled_heat_family P h hh X hX r hr
  refine ⟨Y, hY, ?_⟩
  intro ε
  filter_upwards [hYeq ε] with ω hEq
  apply LSCMetric.ext
  intro p
  rw [B2.LscTop.smulMetric_apply]
  exact normalizedLFPPMetric_dilate_sub_const ξ (m ε)
    (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.property hr)⟩)
    (X ε ω)
    (Y ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.property hr)⟩ ω)
    r hr (circleAvg (h ω) r 0) (hEq) p

end SupercriticalLQGUniqueness.B2.PfeAxioms
