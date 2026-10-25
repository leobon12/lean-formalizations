import SupercriticalLQGUniqueness.B2.DG20Lim.StationaryHeatEventLaw
import SupercriticalLQGUniqueness.B2.DG20Lim.R32ScaledGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatTranslateNormalized
import SupercriticalLQGUniqueness.B2.Polylog.P4Translate

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem translated_finite_good_ratio_bad_prob_le_centerR32
    (ξ : ℝ) (a e : Ioi (0 : ℝ))
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (X : DistC → C(ℂ, ℝ)) (hX : IsHeatSmoothing μ id e X)
    (z : ℂ) (A E F : Set ℂ) (C : ℝ≥0∞) :
    let T : ℂ ≃ₜ ℂ := Homeomorph.addRight z
    μ {g | C * LQGMetric.Blueprint.setDist
        (normalizedContLFPP ξ a (X g)) (T '' E) (T '' F) <
      (normalizedContLFPP ξ a (X g)).aroundDist
        (T '' A) (T '' E) (T '' F)} ≤
      μ {g | C * LQGMetric.Blueprint.setDist
        (normalizedContLFPP ξ a (X g)) E F <
      (normalizedContLFPP ξ a (X g)).aroundDist A E F} := by
  let T : ℂ ≃ₜ ℂ := Homeomorph.addRight z
  let R : DistC → DistC := B2.Polylog.recenter z
  let Y : DistC → C(ℂ, ℝ) := fun g =>
    ⟨fun u => X g (u + z) - circleAvg g 1 z,
      ((X g).continuous.comp (by fun_prop : Continuous
        (fun u : ℂ => u + z))).sub continuous_const⟩
  let Ψ : C(ℂ, ℝ) → Prop := fun φ =>
    C * LQGMetric.Blueprint.setDist
      (normalizedContLFPP ξ a φ) E F <
      (normalizedContLFPP ξ a φ).aroundDist A E F
  have hYv : ∀ᵐ g ∂μ, ∀ u, Y g u = heatMollify (e : ℝ) (R g) u := by
    have htr := (B2.DG20Pt.dg20_heat_translate_normalized
      μ id hμ z (e : ℝ) e.property).2
    have hXv := B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify
      μ id hμ e X hX
    filter_upwards [htr, hXv] with g hg hx u
    change X g (u + z) - circleAvg g 1 z =
      heatMollify (e : ℝ) (R g) u
    rw [hx (u + z)]
    simpa only [R, B2.Polylog.recenter,
      translateDist_eq_affineComp_one, id_eq] using (hg u).symm
  have hXv : ∀ᵐ g ∂μ, ∀ u, X g u = heatMollify (e : ℝ) g u :=
    B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify μ id hμ e X hX
  have hR : IsNormalizedWholePlaneGFF R μ := by
    change IsNormalizedWholePlaneGFF
      (fun g => addConst (translateDist z g) (-circleAvg g 1 z)) μ
    simpa only [id_eq] using
      normalized_translate_sub_circleAvg hμ z
  have hlaw : μ.map R = μ := by
    have hh := map_normalized_translate_sub_circleAvg hμ z
    change μ.map (fun g => addConst (translateDist z g)
      (-circleAvg g 1 z)) = μ
    simpa only [Measure.map_id, id_eq] using hh
  have hscale : ∀ g : DistC, Ψ (Y g) ↔
      C * LQGMetric.Blueprint.setDist
        (normalizedContLFPP ξ a (X g)) (T '' E) (T '' F) <
      (normalizedContLFPP ξ a (X g)).aroundDist
        (T '' A) (T '' E) (T '' F) := by
    intro g
    have hφ : ∀ u, Y g u =
        X g (z + (1 : ℂ) * u) + -(circleAvg g 1 z) := by
      intro u
      change X g (u + z) - circleAvg g 1 z =
        X g (z + (1 : ℂ) * u) + -(circleAvg g 1 z)
      simp only [one_mul, sub_eq_add_neg]
      rw [add_comm u z]
    have hT : ∀ u, T u = z + (1 : ℂ) * u := by
      intro u
      change u + z = z + (1 : ℂ) * u
      simp only [one_mul, add_comm]
    exact normalizedContLFPP_good_iff_affine ξ a a
      one_ne_zero (-(circleAvg g 1 z)) hφ T hT A E F C
  change μ {g | C * LQGMetric.Blueprint.setDist
      (normalizedContLFPP ξ a (X g)) (T '' E) (T '' F) <
      (normalizedContLFPP ξ a (X g)).aroundDist
        (T '' A) (T '' E) (T '' F)} ≤
    μ {g | Ψ (X g)}
  calc
    μ {g | C * LQGMetric.Blueprint.setDist
        (normalizedContLFPP ξ a (X g)) (T '' E) (T '' F) <
      (normalizedContLFPP ξ a (X g)).aroundDist
        (T '' A) (T '' E) (T '' F)}
        = μ {g | Ψ (Y g)} := by
          congr 1
          ext g
          exact (hscale g).symm
    _ ≤ μ {g | Ψ (X g)} :=
      measure_le_of_stationary_heat_version R hR.1.measurable.aemeasurable
        hlaw (e : ℝ) Y X hYv hXv Ψ

 

theorem exists_uniform_translated_scaled_good_ratio_tail_of_inputsR32
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (X : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing μ id ε (X ε))
    (η : ℝ) (hη : 0 < η) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
      ∀ z : ℂ, ∀ r : Ioi (0 : ℝ), ∀ δ : Ioo (0 : ℝ) 1,
        (δ : ℝ) < δ₀ →
        let e : Ioi (0 : ℝ) :=
          ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property δ.property.1⟩
        let D : DistC → ContMetric :=
          fun g => normalizedContLFPP (ξ : ℝ) (m e) (X e g)
        let T : ℂ ≃ₜ ℂ := B2.Polylog.dilateHomeo r.property
        let U : ℂ ≃ₜ ℂ := Homeomorph.addRight z
        μ {g | ENNReal.ofReal C *
          LQGMetric.Blueprint.setDist (D g)
            (U '' (T '' unitInnerCircleR32.toSet))
            (U '' (T '' unitOuterCircleR32.toSet)) <
          (D g).aroundDist
            (U '' (T '' unitRatAnnulusR32.toSet))
            (U '' (T '' unitInnerCircleR32.toSet))
            (U '' (T '' unitOuterCircleR32.toSet))} ≤
          ENNReal.ofReal η := by
  obtain ⟨C, δ₀, hC, hδ₀, hscaled⟩ :=
    exists_centered_scaled_good_annulus_ratio_tail_of_inputsR32
      hS4 hPerc ξ Q hQ m hm μ hμ X hX η hη
  refine ⟨C, δ₀, hC, hδ₀, ?_⟩
  intro z r δ hδ
  let e : Ioi (0 : ℝ) :=
    ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property δ.property.1⟩
  let T : ℂ ≃ₜ ℂ := B2.Polylog.dilateHomeo r.property
  let U : ℂ ≃ₜ ℂ := Homeomorph.addRight z
  change μ {g | ENNReal.ofReal C *
      LQGMetric.Blueprint.setDist
        (normalizedContLFPP (ξ : ℝ) (m e) (X e g))
        (U '' (T '' unitInnerCircleR32.toSet))
        (U '' (T '' unitOuterCircleR32.toSet)) <
      (normalizedContLFPP (ξ : ℝ) (m e) (X e g)).aroundDist
        (U '' (T '' unitRatAnnulusR32.toSet))
        (U '' (T '' unitInnerCircleR32.toSet))
        (U '' (T '' unitOuterCircleR32.toSet))} ≤ ENNReal.ofReal η
  have htrans := translated_finite_good_ratio_bad_prob_le_centerR32
    (ξ : ℝ) (m e) e μ hμ (X e) (hX e) z
    (T '' unitRatAnnulusR32.toSet)
    (T '' unitInnerCircleR32.toSet)
    (T '' unitOuterCircleR32.toSet) (ENNReal.ofReal C)
  exact htrans.trans (hscaled r δ hδ)

end SupercriticalLQGUniqueness.B2.DG20Lim
