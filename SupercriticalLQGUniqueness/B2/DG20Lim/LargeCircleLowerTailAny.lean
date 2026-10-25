import SupercriticalLQGUniqueness.B2.DG20Lim.LargeCircleLowerTail
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionBdd

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_large_circle_lower_tail_any_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ e, IsLFPPNormalizer ξ e (m e))
    (T η : ℝ) (hT : 0 < T) (hη : 0 < η) :
    ∃ R₀ ε₀ : ℝ, 1 < R₀ ∧ 0 < ε₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC)
        (hh : IsNormalizedWholePlaneGFF h P)
        (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
        (hX : ∀ e, IsHeatSmoothing P h e (X e))
        (r : Ioi (1 : ℝ)) (e : Ioo (0 : ℝ) 1),
        R₀ ≤ (r : ℝ) → (e : ℝ) < ε₀ →
        P {ω | LQGMetric.Blueprint.setDist
          (normalizedContLFPP (ξ : ℝ)
            (m ⟨(e : ℝ), e.property.1⟩)
            (X ⟨(e : ℝ), e.property.1⟩ ω))
          ((B2.Polylog.dilateHomeo
            (lt_trans one_pos r.property)) '' unitInnerCircle.toSet)
          ((B2.Polylog.dilateHomeo
            (lt_trans one_pos r.property)) '' unitOuterCircle.toSet) <
          ENNReal.ofReal T} ≤ ENNReal.ofReal η := by
  letI : IsProbabilityMeasure normGFFLaw :=
    B2.PfeAxioms.normalized_canonical_model.1
  have hhCan := B2.PfeAxioms.normalized_canonical_model.2
  let H : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ) := canonicalHeatVersion
  have hH : ∀ e, IsHeatSmoothing normGFFLaw id e (H e) := by
    intro e
    have hh : IsGFFPlusBddCont (id : DistC → DistC) normGFFLaw :=
      LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hhCan.1
    obtain ⟨X, hXe, hX⟩ :=
      B2.PfeAxioms.exists_heatVersion_bdd hh e
    intro z
    have hHe := canonicalHeatVersion_ae e
    filter_upwards [hXe, hX z, hHe] with g hg hXg hHg
    dsimp only [H, id] at hg hXg ⊢
    simpa only [hg z, (congrFun hHg z)] using hXg
  obtain ⟨R₀, ε₀, hR₀, hε₀, htail⟩ :=
    exists_large_circle_lower_tail_of_inputs
      hS4 hPerc hPos ξ Q hQ m hm normGFFLaw hhCan H hH T η hT hη
  refine ⟨R₀, ε₀, hR₀, hε₀, ?_⟩
  intro Ω _ P _ h hh X hX r e hr he
  let E : Ioi (0 : ℝ) := ⟨(e : ℝ), e.property.1⟩
  let I : Set ℂ :=
    (B2.Polylog.dilateHomeo (lt_trans one_pos r.property)) ''
      unitInnerCircle.toSet
  let O : Set ℂ :=
    (B2.Polylog.dilateHomeo (lt_trans one_pos r.property)) ''
      unitOuterCircle.toSet
  let F : DistC → ℝ≥0∞ := fun g =>
    LQGMetric.Blueprint.setDist
      (normalizedContLFPP (ξ : ℝ) (m E) (H E g)) I O
  have hFm : Measurable F :=
    (LQGMetric.GM.measurable_setDist I O).comp
      ((measurable_normalizedContLFPP (ξ : ℝ) (m E)).comp
        (canonicalHeatVersion_measurable E))
  have hEvent : P {ω | F (h ω) < ENNReal.ofReal T} =
      normGFFLaw {g | F g < ENNReal.ofReal T} := by
    calc
      P {ω | F (h ω) < ENNReal.ofReal T} =
          (P.map h) {g | F g < ENNReal.ofReal T} :=
        (Measure.map_apply hh.1.measurable
          (measurableSet_Iio.preimage hFm)).symm
      _ = normGFFLaw {g | F g < ENNReal.ofReal T} := by
        rw [B2.PfeAxioms.normGFFLaw_eq_of_normalized P h hh]
  have hXe := ae_heat_version_eq_canonical P h hh E (X E) (hX E)
  calc
    P {ω | LQGMetric.Blueprint.setDist
        (normalizedContLFPP (ξ : ℝ) (m E) (X E ω)) I O <
        ENNReal.ofReal T} ≤ P {ω | F (h ω) < ENNReal.ofReal T} := by
          apply measure_mono_ae
          filter_upwards [hXe] with ω hω hw
          simpa only [F, H, hω] using hw
    _ = normGFFLaw {g | F g < ENNReal.ofReal T} := hEvent
    _ ≤ ENNReal.ofReal η := by
      simpa only [F, H, E, I, O] using htail r e hr he

end SupercriticalLQGUniqueness.B2.DG20Lim
