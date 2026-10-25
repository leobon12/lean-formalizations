import SupercriticalLQGUniqueness.B2.DG20Lim.FieldMarginal
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedLaw

 


set_option autoImplicit false
noncomputable section

open MeasureTheory LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

private theorem exists_canonical_heat_version
    (δ : Set.Ioi (0 : ℝ)) :
    ∃ H : DistC → C(ℂ, ℝ), Measurable H ∧
      ∀ᵐ g ∂normGFFLaw, (H g : ℂ → ℝ) = heatMollify (δ : ℝ) g := by
  have hm : Measurable (fun g : DistC => heatMollify (δ : ℝ) g) :=
    measurable_pi_iff.mpr fun z => measurable_heatMollify_left (δ : ℝ) z
  exact B2.PfeAxioms.exists_measurable_continuous_real_version normGFFLaw _ hm
    (LQGMetric.LFPP.ae_continuous_heatMollify_normGFFLaw δ.property.ne')

 
def canonicalHeatVersion (δ : Set.Ioi (0 : ℝ)) : DistC → C(ℂ, ℝ) :=
  (exists_canonical_heat_version δ).choose

theorem canonicalHeatVersion_measurable (δ : Set.Ioi (0 : ℝ)) :
    Measurable (canonicalHeatVersion δ) :=
  (exists_canonical_heat_version δ).choose_spec.1

theorem canonicalHeatVersion_ae (δ : Set.Ioi (0 : ℝ)) :
    ∀ᵐ g ∂normGFFLaw,
      (canonicalHeatVersion δ g : ℂ → ℝ) = heatMollify (δ : ℝ) g :=
  (exists_canonical_heat_version δ).choose_spec.2

theorem ae_heat_version_eq_canonical
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (δ : Set.Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h δ X) :
    ∀ᵐ ω ∂P, X ω = canonicalHeatVersion δ (h ω) := by
  have hCanon := canonicalHeatVersion_ae δ
  rw [B2.PfeAxioms.normGFFLaw_eq_of_normalized P h hh] at hCanon
  have hCanon' := ae_of_ae_map hh.1.measurable.aemeasurable hCanon
  have hXeq := DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh δ X hX
  filter_upwards [hCanon', hXeq] with ω hc hx
  apply ContinuousMap.ext
  intro z
  exact (hx z).trans (congrFun hc z).symm

 
theorem joint_law_normalizedContLFPP_eq_canonical
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (δ a : Set.Ioi (0 : ℝ)) (ξ : ℝ)
    (X : Ω → C(ℂ, ℝ)) (hX : IsHeatSmoothing P h δ X) :
    P.map (fun ω => (h ω, normalizedContLFPP ξ a (X ω))) =
      normGFFLaw.map (fun g =>
        (g, normalizedContLFPP ξ a (canonicalHeatVersion δ g))) := by
  have hCanon : Measurable (fun g : DistC =>
      (g, normalizedContLFPP ξ a (canonicalHeatVersion δ g))) :=
    measurable_id.prodMk
      ((measurable_normalizedContLFPP ξ a).comp
        (canonicalHeatVersion_measurable δ))
  calc
    P.map (fun ω => (h ω, normalizedContLFPP ξ a (X ω))) =
        P.map (fun ω =>
          (h ω, normalizedContLFPP ξ a (canonicalHeatVersion δ (h ω)))) := by
          apply Measure.map_congr
          filter_upwards [ae_heat_version_eq_canonical P h hh δ X hX] with ω hω
          simp only [hω]
    _ = (P.map h).map (fun g : DistC =>
          (g, normalizedContLFPP ξ a (canonicalHeatVersion δ g))) := by
          exact (Measure.map_map hCanon hh.1.measurable).symm
    _ = normGFFLaw.map (fun g : DistC =>
          (g, normalizedContLFPP ξ a (canonicalHeatVersion δ g))) := by
          rw [B2.PfeAxioms.normGFFLaw_eq_of_normalized P h hh]

end SupercriticalLQGUniqueness.B2.DG20Lim
