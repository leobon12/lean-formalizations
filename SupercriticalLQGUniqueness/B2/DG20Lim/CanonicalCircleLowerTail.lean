import SupercriticalLQGUniqueness.B2.DG20Lim.UnitAnnulusCoords
import SupercriticalLQGUniqueness.B2.DG20Lim.CircleLowerTail
import SupercriticalLQGUniqueness.B2.DG20Lim.CanonicalFiniteLFPP
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCoords
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedCanonicalModel
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionBdd

 


set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

private theorem canonical_heat_isHeatSmoothing (δ : Ioi (0 : ℝ)) :
    IsHeatSmoothing normGFFLaw (id : DistC → DistC) δ
      (canonicalHeatVersion δ) := by
  letI : IsProbabilityMeasure normGFFLaw := B2.PfeAxioms.normalized_canonical_model.1
  have hh : IsGFFPlusBddCont (id : DistC → DistC) normGFFLaw :=
    LQGMetric.DFGPS.isGFFPlusBddCont_of_wp
      B2.PfeAxioms.normalized_canonical_model.2.1
  obtain ⟨X, hXe, hX⟩ := B2.PfeAxioms.exists_heatVersion_bdd hh δ
  intro z
  have hHe := canonicalHeatVersion_ae δ
  filter_upwards [hXe, hX z, hHe] with g hg hXg hHg
  dsimp only [id] at hg hXg ⊢
  simpa only [hg z, (congrFun hHg z)] using hXg

theorem exists_unit_circle_lower_tail_uniform_of_perc
    (hPerc : B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC)
        (hh : IsNormalizedWholePlaneGFF h P)
        (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
        (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
        (ε : Ioo (0 : ℝ) 1), (ε : ℝ) < ε₀ →
      P {ω | finiteCircleCoords
        (normalizedContLFPP (ξ : ℝ)
          (m ⟨ε, ε.property.1⟩) (X ⟨ε, ε.property.1⟩ ω))
        (unitInnerCircle, unitOuterCircle) < ENNReal.ofReal T⁻¹} ≤
        ENNReal.ofReal η := by
  letI : IsProbabilityMeasure normGFFLaw := B2.PfeAxioms.normalized_canonical_model.1
  have hhCan := B2.PfeAxioms.normalized_canonical_model.2
  let H : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ) := canonicalHeatVersion
  have hH : ∀ ε, IsHeatSmoothing normGFFLaw id ε (H ε) :=
    canonical_heat_isHeatSmoothing
  have hdisj : Disjoint unitInnerCircle.toSet unitOuterCircle.toSet := by
    exact RatCircle.disjoint_of_nested unitRatAnnulus.nested
  obtain ⟨T, ε₀, hT, hε₀, htail⟩ :=
    dg20_heat_circle_small_lower_of_perc hPerc ξ m hm normGFFLaw id hhCan
      H hH unitInnerCircle unitOuterCircle hdisj η hη
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro Ω _ P _ h hh X hX ε hε
  let e : Ioi (0 : ℝ) := ⟨ε, ε.property.1⟩
  let F : DistC → ℝ≥0∞ := fun g => finiteCircleCoords
    (normalizedContLFPP (ξ : ℝ) (m e) (H e g))
    (unitInnerCircle, unitOuterCircle)
  have hFm : Measurable F :=
    (measurable_pi_apply (unitInnerCircle, unitOuterCircle)).comp
      (measurable_finiteCircleCoords.comp
        ((measurable_normalizedContLFPP (ξ : ℝ) (m e)).comp
          (canonicalHeatVersion_measurable e)))
  have hLaw : P.map h = normGFFLaw :=
    (B2.PfeAxioms.normGFFLaw_eq_of_normalized P h hh).symm
  have hEvent : P {ω | F (h ω) < ENNReal.ofReal T⁻¹} =
      normGFFLaw {g | F g < ENNReal.ofReal T⁻¹} := by
    calc
      P {ω | F (h ω) < ENNReal.ofReal T⁻¹} =
          (P.map h) {g | F g < ENNReal.ofReal T⁻¹} :=
        (Measure.map_apply hh.1.measurable
          (measurableSet_Iio.preimage hFm)).symm
      _ = normGFFLaw {g | F g < ENNReal.ofReal T⁻¹} := by rw [hLaw]
  have hXe := ae_heat_version_eq_canonical P h hh e (X e) (hX e)
  calc
    P {ω | finiteCircleCoords
        (normalizedContLFPP (ξ : ℝ) (m e) (X e ω))
        (unitInnerCircle, unitOuterCircle) < ENNReal.ofReal T⁻¹} ≤
        P {ω | F (h ω) < ENNReal.ofReal T⁻¹} := by
          apply measure_mono_ae
          filter_upwards [hXe] with ω hω hw
          simpa only [F, H, hω] using hw
    _ = normGFFLaw {g | F g < ENNReal.ofReal T⁻¹} := hEvent
    _ ≤ ENNReal.ofReal η := by simpa only [F, H, e] using htail ε hε

end SupercriticalLQGUniqueness.B2.DG20Lim
