import SupercriticalLQGUniqueness.B2.PfeAxioms.AcrossFiniteLowerTail
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionBdd
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedCanonicalModel
import SupercriticalLQGUniqueness.B2.DG20Lim.CanonicalFiniteLFPP
import LQGMetric.Papers.DFGPS.L2_6Law

 



set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric LQGMetric.DFGPS
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

private theorem canonicalHeatVersion_isHeatSmoothing
    (δ : Ioi (0 : ℝ)) :
    IsHeatSmoothing normGFFLaw (id : DistC → DistC) δ
      (B2.DG20Lim.canonicalHeatVersion δ) := by
  letI : IsProbabilityMeasure normGFFLaw := normalized_canonical_model.1
  have hh : IsGFFPlusBddCont (id : DistC → DistC) normGFFLaw :=
    LQGMetric.DFGPS.isGFFPlusBddCont_of_wp normalized_canonical_model.2.1
  obtain ⟨X, hXe, hX⟩ := exists_heatVersion_bdd hh δ
  intro z
  have hHe := B2.DG20Lim.canonicalHeatVersion_ae δ
  filter_upwards [hXe, hX z, hHe] with g hg hXg hHg
  dsimp only [id] at hg hXg ⊢
  simpa only [hg z, (congrFun hHg z)] using hXg

theorem finite_across_lower_tail_uniform_fieldScale
    (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (A : EuclideanAnnulus) (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ (δ : Ioo (0 : ℝ) 1) (r : ℝ), 0 < r →
      (δ : ℝ) < ε₀ →
      ∀ (Y : Ω → C(ℂ, ℝ)),
        IsHeatSmoothing P (fun ω => fieldScale r (h ω))
          ⟨(δ : ℝ), δ.property.1⟩ Y →
      P {ω | acrossDist
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m ⟨(δ : ℝ), δ.property.1⟩) (Y ω)) A <
          ENNReal.ofReal T⁻¹} ≤ ENNReal.ofReal η := by
  letI : IsProbabilityMeasure normGFFLaw := normalized_canonical_model.1
  have hhCan := normalized_canonical_model.2
  let H : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ) := B2.DG20Lim.canonicalHeatVersion
  have hH : ∀ δ, IsHeatSmoothing normGFFLaw (id : DistC → DistC) δ (H δ) :=
    canonicalHeatVersion_isHeatSmoothing
  obtain ⟨T, ε₀, hT, hε₀, htail⟩ :=
    dg20_heat_across_small_lower_of_perc hPerc ξ m hm
      normGFFLaw id hhCan H hH A η hη
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro δ r hr hδ Y hY
  let e : Ioi (0 : ℝ) := ⟨(δ : ℝ), δ.property.1⟩
  let g : Ω → DistC := fun ω => fieldScale r (h ω)
  have hg : IsNormalizedWholePlaneGFF g P :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalized_new_of_old
      (isNormalizedWPGFF_fieldScale hh.1 hr)
  let F : DistC → ℝ≥0∞ := fun f =>
    acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m e) (H e f)) A
  have hFm : Measurable F :=
    (measurable_acrossDist A).comp
      (measurable_normalizedLFPPMetric_comp (ξ : ℝ) (m e)
        (fun z => (continuous_eval_const z).measurable.comp
          (B2.DG20Lim.canonicalHeatVersion_measurable e)))
  have hLaw : P.map g = normGFFLaw :=
    normGFFLaw_eq_of_normalized P g hg |>.symm
  have hEvent : P {ω | F (g ω) < ENNReal.ofReal T⁻¹} =
      normGFFLaw {f | F f < ENNReal.ofReal T⁻¹} := by
    calc
      P {ω | F (g ω) < ENNReal.ofReal T⁻¹} =
          (P.map g) {f | F f < ENNReal.ofReal T⁻¹} :=
        (Measure.map_apply hg.1.measurable
          (measurableSet_Iio.preimage hFm)).symm
      _ = normGFFLaw {f | F f < ENNReal.ofReal T⁻¹} := by rw [hLaw]
  have hYe := B2.DG20Lim.ae_heat_version_eq_canonical P g hg e Y hY
  calc
    P {ω | acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
        (m e) (Y ω)) A < ENNReal.ofReal T⁻¹} ≤
        P {ω | F (g ω) < ENNReal.ofReal T⁻¹} := by
          apply measure_mono_ae
          filter_upwards [hYe] with ω hω hw
          simpa only [F, hω] using hw
    _ = normGFFLaw {f | F f < ENNReal.ofReal T⁻¹} := hEvent
    _ ≤ ENNReal.ofReal η := by
      simpa only [F, H, e] using htail δ hδ

end SupercriticalLQGUniqueness.B2.PfeAxioms
