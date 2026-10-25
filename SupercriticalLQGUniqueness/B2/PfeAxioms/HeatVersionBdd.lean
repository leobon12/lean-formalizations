import SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint
import LQGMetric.Field.HeatMollifyUnif

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_heatVersion_bdd
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    (ε : Ioi (0 : ℝ)) :
    ∃ Y : Ω → C(ℂ, ℝ),
      (∀ᵐ ω ∂P, ∀ z : ℂ,
        Y ω z = heatMollify (ε : ℝ) (h ω) z) ∧
      IsHeatSmoothing P h ε Y := by
  classical
  let Y : Ω → C(ℂ, ℝ) := fun ω =>
    if hc : Continuous (heatMollify (ε : ℝ) (h ω)) then
      ⟨heatMollify (ε : ℝ) (h ω), hc⟩ else 0
  refine ⟨Y, ?_, ?_⟩
  · filter_upwards [hh.ae_tendstoLocallyUniformly_heatMollify
      (ε : ℝ) ε.property.ne'] with ω hω z
    simp only [Y, dif_pos hω.2, ContinuousMap.coe_mk]
  · intro z
    filter_upwards [hh.ae_tendstoLocallyUniformly_heatMollify
      (ε : ℝ) ε.property.ne',
      hh.ae_tendsto_heatMollify (ε : ℝ) ε.property.ne' z]
      with ω hcont hlim
    simpa only [positiveHeatTrunc, Y, dif_pos hcont.2,
      ContinuousMap.coe_mk] using hlim

theorem ae_heatVersion_eq_heatMollify_bdd
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    (ε : Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h ε X) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      X ω z = heatMollify (ε : ℝ) (h ω) z := by
  obtain ⟨Y, hYe, hY⟩ := exists_heatVersion_bdd hh ε
  have hXY := SupercriticalLQGUniqueness.Exponent.HeatVersion.ae_eq_continuous_heat_versions
    (ε : ℝ) ε.property X Y hX hY
  filter_upwards [hXY, hYe] with ω hEq hYω
  intro z
  rw [hEq]
  exact hYω z

end SupercriticalLQGUniqueness.B2.PfeAxioms
