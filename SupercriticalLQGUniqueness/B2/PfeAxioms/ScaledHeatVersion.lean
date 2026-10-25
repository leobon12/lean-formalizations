import SupercriticalLQGUniqueness.B2.PfeAxioms.LFPPSetFieldScale
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge
import LQGMetric.Papers.DFGPS.L2_10Proof

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric LQGMetric.DFGPS
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_scaled_heat_family
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (r : ℝ) (hr : 0 < r) :
    let g : Ω → DistC := fun ω => fieldScale r (h ω)
    ∃ Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ δ, IsHeatSmoothing P g δ (Y δ)) ∧
      ∀ ε : Ioi (0 : ℝ), ∀ᵐ ω ∂P, ∀ z,
        Y ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.property hr)⟩ ω z =
          X ε ω ((r : ℂ) * z) - circleAvg (h ω) r 0 := by
  dsimp
  let g : Ω → DistC := fun ω => fieldScale r (h ω)
  have hg : IsNormalizedWholePlaneGFF g P :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalized_new_of_old
      (isNormalizedWPGFF_fieldScale hh.1 hr)
  have hchoice : ∀ δ : Ioi (0 : ℝ), ∃ Z : Ω → C(ℂ, ℝ),
      (∀ᵐ ω ∂P, ∀ z, Z ω z = heatMollify δ (g ω) z) ∧
      IsHeatSmoothing P g δ Z := by
    intro δ
    exact exists_heatVersion hg δ δ.property
  let Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun δ => (hchoice δ).choose
  refine ⟨Y, (fun δ => (hchoice δ).choose_spec.2), ?_⟩
  intro ε
  let δ : Ioi (0 : ℝ) :=
    ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.property hr)⟩
  have hYeq := (hchoice δ).choose_spec.1
  have hXeq := B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh ε (X ε) (hX ε)
  have hAff := ae_heatMollify_affineComp hh.1 ε.property.ne' hr
  have hConv := (hh.1.affineComp hr 0).ae_tendstoLocallyUniformly_heatMollify
    ((ε : ℝ) / r) (div_ne_zero ε.property.ne' hr.ne')
  filter_upwards [hYeq, hXeq, hAff, hConv] with ω hYω hXω hAffω hConvω
  intro z
  rw [hYω z]
  change heatMollify ((ε : ℝ) / r)
    (addConst (affineComp r 0 (h ω)) (-circleAvg (h ω) r 0)) z = _
  rw [heatMollify_addConst_of_tendsto (div_ne_zero ε.property.ne' hr.ne')
    ((tendstoLocallyUniformlyOn_univ.2 hConvω.1).tendsto_at (mem_univ z))]
  rw [hAffω z, hXω ((r : ℂ) * z)]
  ring

end SupercriticalLQGUniqueness.B2.PfeAxioms
